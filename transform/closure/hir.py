from typing import TypeAlias, cast
from enum import Enum, auto
from collections.abc import Iterable, Sequence
from opkinds import BinaryOpKind
import transform.closure.lirgenerator as lirgenerator
from transform.closure.valuetype import ValueType, IntType, FloatType, TupleType, IntConstant, FloatConstant, ArrayType
from collections import deque
from id import Id


current_block_id = 0


def get_next_block_id():
    global current_block_id
    res = current_block_id
    current_block_id += 1
    return res


current_instruction_id = 0


def get_next_instruction_id():
    global current_instruction_id
    res = current_instruction_id
    current_instruction_id += 1
    return res


class Instruction:
    def __init__(self, type: ValueType | None, block: 'BlockBegin') -> None:
        self.__id = get_next_instruction_id()
        self.__use_count = 0
        self.__type = type
        self.__next: Instruction | None = None  # next instruction in the block. None for BlockEnd instructions
        self.__subst: Instruction | None = None
        self._block = block

    @property
    def id(self): return self.__id

    @property
    def block(self): return self._block

    @property
    def type(self) -> ValueType | None: return self.__type

    @property
    def next(self): return self.__next

    @next.setter
    def next(self, value: 'Instruction'):
        assert not isinstance(self, BlockEnd)
        self.__next = value
        value._block = self._block

    @property
    def use_count(self): return self.__use_count

    @use_count.setter
    def use_count(self, value: int): self.__use_count = value

    @property
    def subst(self) -> 'Instruction': return self.__subst.subst if self.__subst is not None else self

    def replace_uses(self, old: 'Value', new: 'Value') -> bool:
        assert (old.type is new.type is None) or (old.type is not None and new.type is not None and old.type.base() == new.type.base())
        return False

    @subst.setter
    def subst(self, subst: 'Instruction') -> None: 
        match self.type, subst.type:
            case ValueType() as t, ValueType() as s:
                assert t.base() == s.base()
            case None, None:
                ...
            case _, _:
                raise ValueError(f"cannot substitute {self.type} with {subst.type}")
        self.__subst = subst
        

    def insert_after(self, i: 'Instruction'):
        n = self.__next
        self.next = i
        if n is not None:
            i.next = n

    def input_values(self) -> Sequence['Value']:
        return ()
    
    def __repr__(self) -> str:
        if self.type is not None:
            return f'{self.type.tchar()}{self.id}'
        else:
            return f'_{self.id}'


Value: TypeAlias = Instruction


class StateSplit(Instruction):
    def __init__(self, type: ValueType | None, block: 'BlockBegin') -> None:
        super().__init__(type, block)


class BlockBegin(StateSplit):

    def __init__(self):
        super().__init__(None, self)
        self.__block_id = get_next_block_id()
        self.__is_entry = False
        self.__depth_first_number = -1
        self.__linearscan_number = -1
        self.__dominator_depth = -1
        self.__is_loop_header = False
        self.__is_loop_end = False
        self.__loop_depth = 0
        self.__loop_index = -1
        # fields used by BlockListBuilder
        # self.__total_preds = 0
        # self.__stores_to_locals = 0
        # SSA specific fields
        self.__predesessors: list[BlockBegin] = []
        self.__dominates = []
        self.__dominator = None
        self.__end: BlockEnd | None = None
        self.lir: lirgenerator.LIRList = lirgenerator.LIRList(self)
        self.__live_in = 0
        self.__live_out = 0
        self.__live_gen = 0
        self.__live_kill = 0

    def set_loop_info(self, is_header: bool, is_end: bool, index: int, depth: int):
        assert not (is_header and is_end)
        self.__is_loop_header, self.__is_loop_end, self.__loop_index, self.__loop_depth = is_header, is_end, index, depth
    @property
    def is_loop_header(self): return self.__is_loop_header
    @property
    def is_loop_end(self): return self.__is_loop_end
    @property
    def loop_index(self): return self.__loop_index
    @property
    def loop_depth(self): return self.__loop_depth
    @property
    def block_id(self): return self.__block_id

    @property
    def predesessors(self):
        return self.__predesessors

    @property
    def is_entry(self):
        return self.__is_entry

    def set_as_entry(self):
        self.__is_entry = True
    
    def split_entry(self):
        assert self.is_entry and not self.__predesessors
        self.__is_entry = False
        entry = BlockBegin()
        entry.__is_entry = True
        entry.next = entry.end = Goto(self, entry)
        self.__predesessors.append(entry)
        return entry

    @property
    def end(self):
        assert self.__end is not None
        return self.__end

    @end.setter
    def end(self, value: 'BlockEnd'):
        assert isinstance(value, BlockEnd)
        self.__end = value

    def __repr__(self):
        return f"B{self.__block_id}"


class BlockEnd(Instruction):
    def __init__(self, type: ValueType | None, block: BlockBegin, sux: list[BlockBegin]) -> None:
        super().__init__(type, block)
        self.__sux = list(sux)

    @property
    def begin(self): return self._block
    @property
    def sux(self): return self.__sux

    @property
    def next(self):
        return None

    @next.setter
    def next(self, value: Instruction | None):
        if value is not None:
            raise RuntimeError(f"{type(self)} instructions cannot have a next instruction")


class Goto(BlockEnd):
    class Direction(Enum):
        none = auto()  # just a regular goto
        taken = auto()  # goto produced from If
        not_taken = auto()  # goto produced from If

    def __init__(self, sux: BlockBegin, block: BlockBegin) -> None:
        super(Goto, self).__init__(None, block, [sux])
        self.__direction = Goto.Direction.none

    @property
    def direction(self): return self.__direction
    
    @direction.setter
    def direction(self, value: 'Goto.Direction'): self.__direction = value

    def __str__(self) -> str:
        match self.direction:
            case Goto.Direction.none:
                return f"goto {self.sux[0]}"
            case Goto.Direction.taken:
                return f"goto {self.sux[0]} (taken)"
            case Goto.Direction.not_taken:
                return f"goto {self.sux[0]} (not taken)"


class Condition(Enum):
    """Enumeration of possible conditions in a conditional branch."""
    EQL = auto()
    NEQ = auto()
    LSS = auto()
    LEQ = auto()
    GTR = auto()
    GEQ = auto()

    def mirror(self):
        return {
            Condition.EQL: Condition.EQL,
            Condition.NEQ: Condition.NEQ,
            Condition.LSS: Condition.GEQ,
            Condition.LEQ: Condition.GTR,
            Condition.GTR: Condition.LEQ,
            Condition.GEQ: Condition.LSS
        }[self]

    def negate(self):
        return {
            Condition.EQL: Condition.NEQ,
            Condition.NEQ: Condition.EQL,
            Condition.LSS: Condition.GEQ,
            Condition.LEQ: Condition.GTR,
            Condition.GTR: Condition.LEQ,
            Condition.GEQ: Condition.LSS
        }[self]

    def as_binary_op(self):
        return {
            Condition.EQL: BinaryOpKind.I_EQ,
            Condition.NEQ: BinaryOpKind.I_NEQ,
            Condition.LSS: BinaryOpKind.I_LT,
            Condition.LEQ: BinaryOpKind.I_LE,
            Condition.GTR: BinaryOpKind.I_GT,
            Condition.GEQ: BinaryOpKind.I_GE
        }[self]
    
    def __str__(self) -> str:
        return {
            Condition.EQL: "=",
            Condition.NEQ: "<>",
            Condition.LSS: "<",
            Condition.LEQ: "<=",
            Condition.GTR: ">",
            Condition.GEQ: ">="
        }[self]


class If(BlockEnd):

    def __init__(self, x: Value, cond: Condition, y: Value, tsux: BlockBegin, fsux: BlockBegin, block: BlockBegin) -> None:
        """
        creation
        """
        super().__init__(None, block, [tsux, fsux])
        assert isinstance(x.type, IntType) and isinstance(y.type, IntType)
        self.__x = x
        self.__cond = cond
        self.__y = y
        self.__swapped = False
    
    @property
    def x(self): return self.__x

    @property
    def cond(self): return self.__cond

    @property
    def y(self): return self.__y

    def replace_uses(self, old: Instruction, new: Instruction):
        super().replace_uses(old, new)
        res = False
        if self.__x is old and old is not new: self.__x = new; res = True
        if self.__y is old and old is not new: self.__y = new; res = True
        return res

    def swap_operands(self):
        self.__x, self.__y = self.__y, self.__x
        self.__cond = self.__cond.mirror()
        self.__swapped = not self.__swapped

    def input_values(self):
        return self.__x, self.__y
    
    def __str__(self) -> str:
        return f"if {self.__x} {self.__cond} {self.__y} then B{self.sux[0].block_id} else B{self.sux[1].block_id}"


class Return(BlockEnd):
    def __init__(self, value: Value | None, block: BlockBegin) -> None:
        super().__init__(None, block, [])
        if value is not None and value.type is not None:
            self.__value = value
        else:
            self.__value = None
    
    @property
    def value(self): return self.__value

    def replace_uses(self, old: Value, new: Value) -> bool:
        super().replace_uses(old, new)
        if self.__value is old and old is not new: self.__value = new; return True
        return False

    def input_values(self):
        return (self.value,) if self.value is not None else ()

class Op2(Instruction):
    def __init__(self, type: ValueType | None, op: BinaryOpKind, x: Value, y: Value, block: BlockBegin) -> None:
        super().__init__(type, block)
        self.__op, self.__x, self.__y = op, x, y

    @property
    def op(self): return self.__op

    @property
    def x(self): return self.__x
    
    @property
    def y(self): return self.__y

    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.__x is old and old is not new: self.__x = new; res = True
        if self.__y is old and old is not new: self.__y = new; res = True
        return res

    def input_values(self) -> Sequence[Value]:
        return self.__x, self.__y


class NegateOp(Instruction):
    def __init__(self, x: Value, block: BlockBegin):
        super().__init__(x.type, block)
        self.__x = x
    
    @property
    def x(self): return self.__x

    def replace_uses(self, old: Value, new: Value) -> bool:
        super().replace_uses(old, new)
        if self.__x is old and old is not new: self.__x = new; return True
        return False

    def input_values(self):
        return self.__x,


class ArithmeticOp(Op2):
    ...


class CompareOp(Op2):
    ...


class LogicOp(Op2):
    ...


class ShiftOp(Op2):
    ...


class IfOp(Op2):
    def __init__(self, x: Value, cond: Condition, y: Value, tval: Value, fval: Value, block: BlockBegin):
        super().__init__(IfOp.meet(tval.type, fval.type), cond.as_binary_op(), x, y, block)
        self.__cond, self.__tval, self.__fval = cond, tval, fval

    @property
    def cond(self): return self.__cond

    @property
    def tval(self): return self.__tval

    @property   
    def fval(self): return self.__fval

    @staticmethod
    def meet(a: ValueType | None, b: ValueType | None):
        match a, b:
            case IntType(), IntType():
                return IntType()
            case _:
                raise ValueError(f"cannot meet {a} and {b}")
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.__tval is old and old is not new: self.__tval = new; res = True
        if self.__fval is old and old is not new: self.__fval = new; res = True
        return res

    def input_values(self):
        return self.x, self.y, self.__tval, self.__fval


class Convert(Instruction):
    def __init__(self, x: Value, to_type: IntType | FloatType, block: BlockBegin):
        assert isinstance(x.type, (IntType, FloatType))
        super().__init__(to_type.base(), block)
        self.__value = x

    @property
    def value(self): return self.__value

    def replace_uses(self, old: Value, new: Value) -> bool:
        super().replace_uses(old, new)
        if self.__value is old and old is not new: self.__value = new; return True
        return False

    def input_values(self): return self.__value,


class Phi(Instruction):
    def __init__(self, type: ValueType, preds: list[Value], block: BlockBegin):
        super().__init__(type.base(), block)
        self.__preds = list(preds)
    
    @property
    def preds(self): return self.__preds

    def replace_uses(self, old: 'Value', new: 'Value') -> bool:
        super().replace_uses(old, new)
        if old in self.__preds and old is not new:
            for i, x in enumerate(self.__preds):
                if x is old:
                    self.__preds[i] = new
            return True
        return False

    def __getitem__(self, i: int):
        return self._block.predesessors[i].end
    
    def input_values(self): return self.__preds


class Constant(Instruction):
    __match_args__ = 'value',
    def __init__(self, type: IntConstant | FloatConstant, block: BlockBegin):
        super().__init__(type, block)
    
    @property
    def basic_type(self):
        return cast(IntConstant | FloatConstant, self.type).to_basic_types()[0]

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Constant) and self.type == other.type
    
    def __hash__(self) -> int:
        return hash((Constant, self.basic_type, cast(IntConstant | FloatConstant, self.type).value))
    
    @property
    def value(self):
        assert isinstance(self.type, (IntConstant, FloatConstant))
        return self.type.value

    def __repr__(self):
        assert isinstance(self.type, (IntConstant, FloatConstant))
        return f"Constant({self.type.value})"


class Local(Instruction):
    def __init__(self, type: ValueType, name: Id, offset: int, block: BlockBegin):
        """offset: offset in words from the frame pointer."""
        super().__init__(type, block)
        self.name = name
        self.offset = offset

    def __repr__(self):
        return f"Local({self.name}, {self.offset}, {self.type})"


class NewTuple(Instruction):
    def __init__(self, elems: tuple[Value, ...], block: BlockBegin):
        assert all(isinstance(x.type, ValueType) for x in elems)
        super().__init__(TupleType(tuple(x.type or IntType() for x in elems)), block)
        self.__elems = tuple(elems)
    
    @property
    def elems(self): return self.__elems

    def replace_uses(self, old: Value, new: Value) -> bool:
        super().replace_uses(old, new)
        if old in self.__elems and old is not new:
            self.__elems = tuple(new if x is old else x for x in self.__elems)
            return True
        return False
    
    def input_values(self): return self.__elems


class NewArray(Instruction):
    def __init__(self, size: Value, init: Value, block: BlockBegin):
        assert isinstance(size.type, IntType) and init.type is not None
        super().__init__(ArrayType(init.type.base()), block)
        self.__size, self.__init = size, init
    @property
    def size(self): return self.__size
    @property
    def init(self): return self.__init

    def replace_uses(self, old: Value, new: Value) -> bool:
        super().replace_uses(old, new)
        if self.__size is old and old is not new: self.__size = new; return True
        if self.__init is old and old is not new: self.__init = new; return True
        return False

    def input_values(self): return self.__size, self.__init


class AccessField(Instruction):
    def __init__(self, type: ValueType | None, obj: Value, offset: int, block: BlockBegin):
        """offset: offset in words from the object pointer."""
        super().__init__(type, block)
        self.__obj, self.__offset = obj, offset

    @property
    def obj(self): return self.__obj
    @property
    def offset(self): return self.__offset

    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.__obj is old and old is not new: self.__obj = new; res = True
        return res


class LoadField(AccessField):

    def __init__(self, type: ValueType, obj: Value, offset: int, block: BlockBegin):
        super().__init__(type, obj, offset, block)

    def __str__(self) -> str:
        return f"{self.obj}.offset({self.offset})"
    
    def input_values(self):
        return self.obj, 



class StoreField(AccessField):
    
    def __init__(self, obj: Value, offset: int, value: Value, block: BlockBegin):
        assert value.type is not None
        super().__init__(None, obj, offset, block)
        self.value = value

    def input_values(self):
        return self.obj, self.value
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.value is old and old is not new: self.value = new; res = True
        return res


class AccessIndexed(Instruction):
    def __init__(self, type: ValueType | None, array: Value, index: Value, block: BlockBegin):
        super().__init__(type, block)
        self.array = array
        self.index = index
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.array is old and old is not new: self.array = new; res = True
        if self.index is old and old is not new: self.index = new; res = True
        return res


class LoadIndexed(AccessIndexed):
    def __init__(self, array: Value, index: Value, elt_type: ValueType, block: BlockBegin):
        super().__init__(elt_type, array, index, block)
    
    def input_values(self):
        return self.array, self.index


class StoreIndexed(AccessIndexed):
    def __init__(self, array: Value, index: Value, value: Value, block: BlockBegin):
        assert value.type is not None
        super().__init__(None, array, index, block)
        self.value = value
    
    def input_values(self):
        return self.array, self.index, self.value
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.value is old and old is not new: self.value = new; res = True
        return res


class AccessGlobal(Instruction):
    def __init__(self, name: Id, type: ValueType | None, block: BlockBegin):
        super().__init__(type, block)
        self.name = name


class LoadGlobal(AccessGlobal):
    def __init__(self, name: Id, type: ValueType, block: BlockBegin):
        super().__init__(name, type, block)


class StoreGlobal(AccessGlobal):
    def __init__(self, name: Id, value: Value, block: BlockBegin):
        assert value.type is not None
        super().__init__(name, None, block)
        self.value = value
    
    def input_values(self):
        return self.value,

    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.value is old and old is not new: self.value = new; res = True
        return res


class Function:
    def __init__(self, name: Id, ret: ValueType | None, formal_args: Iterable[Local], formal_fv: Local | None, load_fv_fields: Iterable[LoadField],
                 entry: BlockBegin):
        self.name = name
        self.ret_type = ret
        self.entry = entry
        assert entry.is_entry
        self.formal_args = tuple(formal_args)
        self.formal_fv = formal_fv
        self.load_fv_fields = tuple(load_fv_fields)
        assert (self.formal_fv is None) == (len(self.load_fv_fields) == 0)

    def gen_lir(self):
        self.entry.lir.reset()
        self.formal_arg_vregs = sum((tuple(self.entry.lir.local(a)) for a in self.formal_args), ())
        if self.formal_fv is not None:
            self.entry.lir.local(self.formal_fv)
            raise NotImplementedError("TODO: load fields of formal free variable")
        self.entry.lir.gen_lir(self, set(), ())
        self.entry.lir.gen_patch_moves()
        self.entry.lir.apply_patch_moves()
    
    def __repr__(self):
        return f"Function({self.name}, {self.ret_type}, {self.formal_args}, {self.formal_fv}, {self.entry})"

    def collect_all_blocks(self):
        visited = {self.entry.block_id: self.entry}
        q = deque([self.entry])
        while q:
            cur = q.popleft()
            for succ in cur.end.sux:
                if succ.block_id not in visited:
                    visited[succ.block_id] = succ
                    q.append(succ)
        return visited


class InvokeStatic(Instruction):
    def __init__(self, receiver: Function, args: list[Value], block: BlockBegin):
        super().__init__(receiver.ret_type, block)
        self.__receiver = receiver
        self.__args = list(args)
        self.__tail = False
    @property
    def receiver(self): return self.__receiver
    @property
    def args(self): return self.__args
    @property
    def tail(self): return self.__tail
    @tail.setter
    def tail(self, value: bool): self.__tail = value

    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if old in self.__args and old is not new:
            for i, x in enumerate(self.__args):
                if x is old:
                    self.__args[i] = new
                    res = True
        return res

    def input_values(self):
        return self.__args


class FloatPrimitive(Instruction):
    name: str
    __match_args__ = 'arg',

    def __init__(self, arg: Value, block: BlockBegin):
        assert isinstance(arg.type, FloatType)
        super().__init__(FloatType(), block)
        self.arg = arg
    
    def __str__(self) -> str:
        return f'{self.name} ({self.arg})'
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.arg is old and old is not new: self.arg = new; res = True
        return res
    
    def input_values(self):
        return self.arg,


class Fabs(FloatPrimitive):
    name = "fabs"


class Floor(FloatPrimitive):
    name = "floor"


class Sin(FloatPrimitive):
    name = "sin"


class Cos(FloatPrimitive):
    name = "cos"


class Sqrt(FloatPrimitive):
    name = "sqrt"


class Atan(FloatPrimitive):
    name = "atan"


class IO(Instruction):
    ...


class PrintInt(IO):
    def __init__(self, arg: Value, block: BlockBegin):
        assert isinstance(arg.type, IntType)
        super().__init__(None, block)
        self.arg = arg
    
    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.arg is old and old is not new: self.arg = new; res = True
        return res  
    
    def input_values(self):
        return self.arg,


class PrintByte(IO):
    def __init__(self, arg: Value, block: BlockBegin):
        assert isinstance(arg.type, IntType)
        super().__init__(None, block)
        self.arg = arg

    def replace_uses(self, old: Value, new: Value) -> bool:
        res = super().replace_uses(old, new)
        if self.arg is old and old is not new: self.arg = new; res = True
        return res

    def input_values(self):
        return self.arg,


class ReadInt(IO):
    def __init__(self, block: BlockBegin):
        super().__init__(IntType(), block)


class ReadFloat(IO):
    def __init__(self, block: BlockBegin):
        super().__init__(FloatType(), block)
