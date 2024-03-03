import transform.closure.language as l
from id import Id
from ty import Ty, TyUnit, TyInt, TyFloat, TyBool, TyFun, TyTuple, TyArray
from transform.closure.hir import *
from transform.closure.valuetype import ValueType, IntType, FloatType, ArrayType, TupleType, ClosureType

from typing import overload, Literal, TypeVar, cast
from io import TextIOWrapper
from collections import ChainMap
from opkinds import BinaryOpKind
from collections.abc import Iterable, Mapping
from logging import getLogger

logger = getLogger(__name__)
logger.setLevel('ERROR')

T = TypeVar('T', bound=Value)

def to_value_type(t: Ty, /) -> ValueType | None:
    match t:
        case TyInt() | TyBool():
            return IntType()
        case TyFloat():
            return FloatType()
        case TyArray(elem):
            return ArrayType(to_value_type(elem) or IntType())
        case TyTuple(elems):
            match tuple(x for x in map(to_value_type, elems) if x is not None):
                case []:
                    return None
                case [x]:
                    return x
                case xs:
                    return TupleType(xs)
        case TyUnit():
            return
        case TyFun(args, ret):
            a = tuple(x for x in map(to_value_type, args) if x is not None)
            r = to_value_type(ret)
            return ClosureType(a, r)
        case _:
            raise ValueError(t)
        
def offset_at(t: TupleType, i: int, /) -> int:
    assert 0 <= i < len(t.elems)
    return sum(x.abi_size for x in t.elems[:i])



class BlockListBuilder:
    def __init__(self, fns: Mapping[Id, Function], array_makes: Mapping[Id, Ty], globals: Mapping[Id, ValueType]):
        self.__cur = BlockBegin()
        self.__blocks: list[BlockBegin] = [self.__cur]
        self.__lasts: list[Instruction] = [self.__cur]
        self.__successors: list[tuple[BlockBegin, list[BlockBegin]]] = [(self.__cur, [])]
        self.__env: ChainMap[Id, Instruction | None] = ChainMap()
        self.__globals = globals
        self.__fns = fns
        self.__array_makes = array_makes
    
    def initialize(self, entry: BlockBegin, /):
        self.__cur = entry
        self.__blocks.clear()
        self.__blocks.append(entry)
        self.__lasts.clear()
        self.__lasts.append(entry)
        self.__env.clear()
        self.__successors.clear()
        self.__successors.append((entry, []))
    
    @property
    def blocks(self):
        return self.__blocks
    
    @property
    def globals(self):
        return self.__globals
    
    def create_block(self, *pred: BlockBegin):
        """pred should have no duplicates"""
        b = BlockBegin()
        self.__blocks.append(b)
        self.__lasts.append(b)
        b.predesessors.extend(pred)
        for p in pred:
            self.add_successor(p, b)
        self.__successors.append((b, []))
        return b
    
    def add_successor(self, pred: BlockBegin, succ: BlockBegin):
        for p, s in self.__successors:
            if p is pred:
                if succ not in s:
                    s.append(succ)
                return
        self.__successors.append((pred, [succ]))

    def append(self, i: T, /) -> T:
        assert not isinstance(i, BlockBegin)
        j = self.__blocks.index(self.__cur)
        self.__lasts[j].next = i
        self.__lasts[j] = i
        if isinstance(i, BlockEnd):
            i.block.end = i
        return i
    
    @overload
    def lookup(self, x: Id, /, allow_none: Literal[False] = False) -> Instruction | LoadGlobal:
        ...

    @overload
    def lookup(self, x: Id, /, allow_none: Literal[True]) -> Instruction | LoadGlobal | None:
        ...
    
    def lookup(self, x: Id, /, allow_none: bool = False):
        try:
            v = self.__env[x]
            assert allow_none or v is not None
            return v
        except KeyError:
            y = LoadGlobal(x, self.__globals[x], self.__cur)
            self.append(y)
            self.__env[x] = y
            return y
    
    def int_constant(self, value: int, /):
        return self.append(Constant(IntConstant(value), self.__cur))
    
    def float_constant(self, value: float, /):
        return self.append(Constant(FloatConstant(value), self.__cur))
    
    def load_indexed(self, a: Value, i: Value, elt_type: ValueType, /):
        return self.append(LoadIndexed(a, i, elt_type, self.__cur))
    
    def invoke_static(self, callee: Function, args: list[Value | None], /, tail: bool = False):
        res = self.append(InvokeStatic(callee, [arg for arg in args if arg is not None], self.__cur))
        res.tail = tail
        return res
    
    def if_true(self, cond: Value, tsux: BlockBegin, fsux: BlockBegin, /):
        if isinstance(cond, IfOp):
            x, c, y, tval, fval = cond.x, cond.cond, cond.y, cond.tval, cond.fval
            if isinstance(x, Constant) and not isinstance(y, Constant):
                x, y = y, x
                c = c.mirror()
            match tval.type, fval.type:
                case IntConstant(0), IntConstant(0):
                    goto = self.goto(fsux)
                    goto.direction = Goto.Direction.not_taken
                    return goto
                case IntConstant(_), IntConstant(0):
                    return self.append(If(x, c, y, tsux, fsux, self.__cur))
                case IntConstant(0), IntConstant(_):
                    return self.append(If(x, c, y, fsux, tsux, self.__cur))
                case IntConstant(_), IntConstant(_):
                    goto = self.goto(tsux)
                    goto.direction = Goto.Direction.taken
                    return goto
                case _, _:
                    raise ValueError(cond.tval.type, cond.fval.type)
        elif isinstance(cond, CompareOp) and cond.op == BinaryOpKind.F_NEQ:
            cond = self.compare_op(BinaryOpKind.F_EQ, cond.x, cond.y)
            int_zero = self.int_constant(0)
            return self.append(If(cond, Condition.EQL, int_zero, tsux, fsux, self.__cur))

        int_zero = self.int_constant(0)
        return self.append(If(cond, Condition.NEQ, int_zero, tsux, fsux, self.__cur))
    
    def goto(self, sux: BlockBegin, /):
        return self.append(Goto(sux, self.__cur))
    
    def phi(self, type: ValueType, preds: list[Instruction], /):
        return self.append(Phi(type, preds, self.__cur))
    
    def arithmetic_op(self, type: IntType | FloatType, op: BinaryOpKind, y1: Value, y2: Value, /):
        return self.append(ArithmeticOp(type, op, y1, y2, self.__cur))

    def negate_op(self, y: Value, /):
        if isinstance(y.type, IntConstant):
            return self.int_constant(-y.type.value)
        elif isinstance(y.type, FloatConstant):
            return self.float_constant(-y.type.value)
        return self.append(NegateOp(y, self.__cur))
    
    def shift_op(self, type: ValueType, op: BinaryOpKind, y1: Value, y2: Value, /):
        return self.append(ShiftOp(type, op, y1, y2, self.__cur))
    
    def logic_op(self, type: ValueType, op: BinaryOpKind, y1: Value, y2: Value, /):
        return self.append(LogicOp(type, op, y1, y2, self.__cur))
    
    def compare_op(self, op: BinaryOpKind, y1: Value, y2: Value, /):
        return self.append(CompareOp(IntType(), op, y1, y2, self.__cur))
    
    def convert(self, to_type: IntType | FloatType, y: 'Value', /):
        assert isinstance(to_type, IntType) and isinstance(y.type, FloatType) or isinstance(to_type, FloatType) and isinstance(y.type, IntType)
        return self.append(Convert(y, to_type, self.__cur))
    
    def if_op(self, x: 'Value', cond: 'Condition', y: 'Value', tval: 'Value', fval: 'Value', /):
        if isinstance(x, Constant) and not isinstance(y, Constant):
            x, y = y, x
            cond = cond.mirror()
        return self.append(IfOp(x, cond, y, tval, fval, self.__cur))
    
    def new_tuple(self, elems: Iterable[Value | None], /):
        match [elem for elem in elems if elem is not None]:
            case []:
                return None
            case elems2:
                return self.append(NewTuple(tuple(elems2), self.__cur))
    
    def new_array(self, size: Value, init: Value, /):
        return self.append(NewArray(size, init, self.__cur))

    def load_field(self, x: Value, i: int, /):
        match x.type:
            case TupleType(elems):
                return self.append(LoadField(elems[i], x, offset_at(x.type, i), self.__cur))
            case _:
                raise ValueError(x.type)
            
    def return_(self, value: Value | None, /):
        return self.append(Return(value, self.__cur))
    
    def intrinsic(self, callee: Id, args: list[Value | None], /):
        match args:
            case [None]:
                if callee.is_intrinsic("read_int"):
                    return self.append(ReadInt(self.__cur))
                elif callee.is_intrinsic("read_float"):
                    return self.append(ReadFloat(self.__cur))
                elif callee.is_intrinsic("print_newline"):
                    return self.append(PrintByte(self.int_constant(10), self.__cur))
            case [Value() as x]:
                if callee.is_intrinsic("not"):
                    zero = self.int_constant(0)
                    one = self.int_constant(1)
                    return self.if_op(x, Condition.EQL, zero, one, zero)
                elif callee.is_intrinsic("print_int"):
                    return self.append(PrintInt(x, self.__cur))
                elif callee.is_intrinsic("print_char"):
                    return self.append(PrintByte(x, self.__cur))
                elif callee.is_intrinsic("int_of_float"):
                    return self.convert(IntType(), x)
                elif callee.is_intrinsic("float_of_int"):
                    return self.convert(FloatType(), x)
                elif callee.is_intrinsic("fneg"):
                    return self.negate_op(x)
                elif callee.is_intrinsic("fsqr"):
                    return self.arithmetic_op(FloatType(), BinaryOpKind.F_MUL, x, x)
                elif callee.is_intrinsic("sqrt"):
                    return self.append(Sqrt(x, self.__cur))
                elif callee.is_intrinsic("fispos"):
                    return self.compare_op(BinaryOpKind.F_GT, x, self.float_constant(0.0))
                elif callee.is_intrinsic("fisneg"):
                    return self.compare_op(BinaryOpKind.F_LT, x, self.float_constant(0.0))
                elif callee.is_intrinsic("fiszero"):
                    return self.compare_op(BinaryOpKind.F_EQ, x, self.float_constant(0.0))
                elif callee.is_intrinsic("fabs"):
                    return self.append(Fabs(x, self.__cur))
                elif callee.is_intrinsic("fhalf"):
                    return self.arithmetic_op(FloatType(), BinaryOpKind.F_MUL, x, self.float_constant(0.5))
                elif callee.is_intrinsic("sin"):
                    return self.append(Sin(x, self.__cur))
                elif callee.is_intrinsic("cos"):
                    return self.append(Cos(x, self.__cur))
                elif callee.is_intrinsic("atan"):
                    return self.append(Atan(x, self.__cur))
                elif callee.is_intrinsic("floor"):
                    return self.append(Floor(x, self.__cur))
            case [Value() as x, Value() as y]:
                if callee.is_intrinsic("xor"):
                    return self.logic_op(IntType(), BinaryOpKind.I_XOR, x, y)
                elif callee.is_intrinsic("fless"):
                    return self.compare_op(BinaryOpKind.F_LT, x, y)
                elif callee.is_intrinsic("fequal"):
                    return self.compare_op(BinaryOpKind.F_EQ, x, y)
            case _:
                ...
        raise ValueError(callee, args)

    def visit(self, e: l.Exp[Ty], tail: bool = False) -> tuple[BlockBegin, Value | None]:
        """create all necessary BlockBegin nodes"""
        assert isinstance(self.__cur, BlockBegin)
        match e:
            case l.LitU():
                return self.__cur, None
            case l.LitI() | l.LitB():
                return self.__cur, self.int_constant(e.lit)
            case l.LitF():
                return self.__cur, self.float_constant(e.lit)
            case l.Var():
                return self.__cur, self.lookup(e.name, True)
            case l.Get():
                a, i = self.lookup(e.array), self.lookup(e.index)
                return self.__cur, self.load_indexed(a, i, to_value_type(e.typ) or IntType())
            case l.Unary():
                return self.__cur, self.negate_op(self.lookup(e.y, False))
            case l.AppDir():
                try:
                    f = self.__fns[e.callee]
                except KeyError:
                    if e.callee in self.__array_makes:
                        assert len(e.args) == 2
                        return self.__cur, self.new_array(self.lookup(e.args[0]), self.lookup(e.args[1], True) or self.int_constant(0))
                    else:
                        return self.__cur, self.intrinsic(e.callee, [self.lookup(x, True) for x in e.args])
                        
                return self.__cur, self.invoke_static(f, [self.lookup(x, True) for x in e.args], tail)
            case l.Binary():
                y1, y2 = self.lookup(e.y1), self.lookup(e.y2)
                match e.op:
                    case BinaryOpKind.I_ADD | BinaryOpKind.I_SUB | BinaryOpKind.I_MUL | BinaryOpKind.I_DIV:
                        res =  self.arithmetic_op(IntType(), e.op, y1, y2)
                    case BinaryOpKind.I_SHL | BinaryOpKind.I_SHR: 
                        res =  self.shift_op(IntType(), e.op, y1, y2)
                    case BinaryOpKind.I_AND | BinaryOpKind.I_OR | BinaryOpKind.I_XOR:
                        res = self.logic_op(IntType(), e.op, y1, y2)
                    case BinaryOpKind.F_ADD | BinaryOpKind.F_SUB | BinaryOpKind.F_MUL | BinaryOpKind.F_DIV:
                        res = self.arithmetic_op(FloatType(), e.op, y1, y2)
                    case BinaryOpKind.I_LT:
                        res = self.if_op(y1, Condition.LSS, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.I_LE:
                        res = self.if_op(y1, Condition.LEQ, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.I_EQ | BinaryOpKind.B_EQ:
                        res =  self.if_op(y1, Condition.EQL, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.I_NEQ | BinaryOpKind.B_NEQ:
                        res =  self.if_op(y1, Condition.NEQ, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.I_GE:
                        res =  self.if_op(y1, Condition.GEQ, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.I_GT:
                        res =  self.if_op(y1, Condition.GTR, y2, self.int_constant(1), self.int_constant(0))
                    case BinaryOpKind.F_LT | BinaryOpKind.F_LE | BinaryOpKind.F_EQ | BinaryOpKind.F_NEQ | BinaryOpKind.F_GE | BinaryOpKind.F_GT:
                        res = self.compare_op(e.op, y1, y2)
                    
                return self.__cur, res
            case l.Tuple():
                return self.__cur, self.new_tuple([self.lookup(x, True) for x in e.ys])
            case l.If():
                tsux = self.create_block(self.__cur)
                fsux = self.create_block(self.__cur)
                if_ = self.if_true(self.lookup(e.cond), tsux, fsux)
                if isinstance(if_, Goto):
                    if if_.sux[0] is tsux:
                        return self.visit(e.br_true, tail)
                    return self.visit(e.br_false, tail)

                self.__cur = tsux
                self.__env = self.__env.new_child()
                tsux, tval = self.visit(e.br_true, tail)
                if tail and not isinstance(tval, Return):
                    self.return_(tval)
                
                self.__cur = fsux
                self.__env = self.__env.parents.new_child()
                fsux, fval = self.visit(e.br_false, tail)
                self.__env = self.__env.parents
                
                if tail:
                    if not isinstance(fval, Return):
                        return self.__cur, self.return_(fval)
                    return self.__cur, fval
                else:
                    cont = self.create_block(tsux.block, fsux.block)
                    for p in cont.predesessors:
                        self.__cur = p
                        self.goto(cont)
                        self.add_successor(p, cont)
                    self.__cur = cont
                    match tval, fval:
                        case None, None:
                            return self.__cur, None
                        case [None, val] | [val, None]:
                            assert isinstance(val, Value)
                            if val.type is not None:
                                raise ValueError(tval, fval)
                            return self.__cur, None
                        case tval, fval:
                            match tval.type, fval.type:
                                case None, None:
                                    return self.__cur, None
                                case ValueType() as ttype, ValueType() as ftype:
                                    assert ttype.base() == ftype.base()
                                    return self.__cur, self.phi(ttype.base(), [tval, fval])
                                case _:
                                    raise ValueError(tval.type, fval.type)
            case l.Put():
                a, i, v = self.lookup(e.array), self.lookup(e.index), self.lookup(e.value, True) or self.int_constant(0)
                return self.__cur, self.append(StoreIndexed(a, i, v, self.__cur))
            case l.Seq():
                b: Value | None = None
                for i, x in enumerate(e.es):
                    self.__cur, b = self.visit(x, tail and i == len(e.es) - 1)
                return self.__cur, b
            case l.Let():
                _, self.__env[e.binding.lhs] = self.visit(e.binding.rhs)
                res = self.visit(e.expr, tail)
                del self.__env[e.binding.lhs]
                return res
            case l.LetTuple():
                idx = 0
                for x, t in zip(e.xs, e.ts):
                    if to_value_type(t) is not None:
                        self.__env[x] = self.load_field(self.lookup(e.y), idx)
                        idx += 1
                    else:
                        self.__env[x] = None
                res = self.visit(e.e, tail)
                for x in e.xs:
                    del self.__env[x]
                return res
            case l.MakeCls():
                raise NotImplementedError()
                return self.visit(e.body, tail)
            case _:
                raise ValueError(e)
            
    def visit_LetBinding(self, b: l.LetBinding, /):
        assert len(self.__env) == 0
        assert to_value_type(b.rhs.typ) is None or b.lhs in self.__globals
        _, v = self.visit(b.rhs, False)
        self.__env.clear()
        if v is not None and str(b.lhs) != '_':
            self.append(StoreGlobal(b.lhs, v, self.__cur))
            
    def visit_Function(self, f: Function, body: l.Exp[Ty], /):
        self.initialize(f.entry)
        self.__env.update({local.name: local for local in f.formal_args})
        _, v = self.visit(body, True)
        if v is not None and not isinstance(v, Return):
            self.return_(v)
        assert len(self.__blocks) == len(self.__lasts) == len(self.__successors)
    
    def visit_main(self, main: tuple[l.Exp[Ty] | l.Cls | l.LetBinding, ...], /):
        self.__cur.set_as_entry()
        entry = self.__cur
        for e in main:
            match e:
                case l.Exp() as e:
                    self.visit(e, False)
                case l.Cls():
                    raise NotImplementedError()
                case l.LetBinding() as b:
                    self.visit_LetBinding(b)
        self.append(Return(None, self.__cur))
        return Function(Id("main"), None, [], None, [], entry)


class GraphBuilder:

    @staticmethod
    def to_locals(xs: Iterable[tuple[Id, Ty]], entry: BlockBegin, /):
        locals: list[Local] = []
        word_offset = 0
        for name, t in xs:
            vt = to_value_type(t)
            if vt is not None:
                locals.append(Local(vt, name, word_offset, entry))
                word_offset += vt.abi_size
        return word_offset, locals
    
    def __init__(self, prelude_tys: Mapping[Id, Ty], array_makes: Mapping[Id, Ty], global_vars: Mapping[Id, Ty], prog: l.Program):
        assert prelude_tys.keys().isdisjoint(array_makes.keys())
        assert array_makes.keys().isdisjoint(global_vars.keys())
        assert global_vars.keys().isdisjoint(prelude_tys.keys())
        functions: dict[Id, Function] = {}
        globals: dict[Id, ValueType] = {}
        for k, v in global_vars.items():
            if (vt := to_value_type(v)) is not None:
                globals[k] = vt

        for f in prog.fns:
            entry = BlockBegin()
            entry.set_as_entry()
            _, locals = GraphBuilder.to_locals(zip(f.formal_args, f.typ.args), entry)
            if f.formal_fv:
                raise NotImplementedError()
            functions[f.funct] = Function(f.funct, to_value_type(f.typ.ret), locals, None, [], entry)

        self.__builder = BlockListBuilder(functions, array_makes, globals)
        main = self.__builder.visit_main(prog.exp_or_cls_or_letbindings)
        for f, ff in zip(functions.values(), prog.fns):
            self.__builder.visit_Function(f, ff.body)
        
        self.main = main
        self.functions = functions

    @property
    def globals(self):
        return self.__builder.globals

def str_value(v: Value, fixed_width:int = 0, /):
    tchar = ' ' if v.type is None else v.type.tchar()
    if not fixed_width:
        return f'{tchar}{v.id}'
    return f'{tchar}{v.id:<5}'

class GraphPrinter:
    @staticmethod
    def get_blocks(f: Function, /):
        from collections import deque
        b: BlockBegin = f.entry
        q = deque([b])
        visited = {b.block_id: b}
        while q:
            b = q.popleft()
            for s in b.end.sux:
                if s.block_id not in visited:
                    visited[s.block_id] = s
                    q.append(s)
        return list(visited.values())

    @staticmethod
    def get_instrs(b: BlockBegin, /) -> list[Instruction]:
        instrs: list[Instruction] = []
        i: Value = b
        while i.next is not None:
            instrs.append(i.next)
            i = i.next
        return instrs

    def print_block(self, b: BlockBegin, /, file: TextIOWrapper):
        file.write(f'B{b.block_id}: ')
        if b.predesessors:
            file.write('pred: ')
            file.write(', '.join(f'B{b.block_id}' for b in b.predesessors))
            file.write('; ')
        if b.end.sux:
            file.write('sux: ')
            file.write(', '.join(f'B{b.block_id}' for b in b.end.sux))
            file.write('; ')
        if b.is_entry:
            file.write('entry ')
        if b.loop_index != -1:
            if b.is_loop_header:
                file.write('loop_header ')
            elif b.is_loop_end:
                file.write('loop_end ')
            file.write(f'loop_index {b.loop_index} ')
            file.write(f'loop_depth {b.loop_depth} ')
        file.write('\n')
        instrs = GraphPrinter.get_instrs(b)
        i = 0
        if instrs and isinstance(instrs[0], Phi):
            file.write('  Locals:\n')
        while i < len(instrs) and isinstance((phi:=instrs[i]), Phi):
            phi_v = [f"{str_value(pred)}" for pred in phi.preds]
            print(f'  {phi.use_count:>4} {i}: {str_value(phi, True)}[{", ".join(phi_v)}]', file=file)
            i += 1
        file.write('___use___const___tid_____instr____________\n')
        for i in range(i, len(instrs)):
            instr = instrs[i]
            is_const = '   y   ' if isinstance(instr.type, (IntConstant, FloatConstant)) else '       '
            file.write(f'  {instr.use_count:>4}  {is_const}  {str_value(instr, True)}  ')
            match instr:
                case Constant():
                    s = repr(cast(IntConstant | FloatConstant, instr.type).value)
                case LoadGlobal():
                    s = f'load_global {instr.name}'
                case StoreGlobal():
                    s = f'store_global {instr.name} <- {str_value(instr.value)}'
                case LoadIndexed():
                    s = f'{str_value(instr.array)}.({str_value(instr.index)})'
                case StoreIndexed():
                    s = f'{str_value(instr.array)}.({str_value(instr.index)}) <- {str_value(instr.value)}'
                case LoadField():
                    s = f'{str_value(instr.obj)}:{instr.offset}'
                case InvokeStatic():
                    tail = 'tail ' if instr.tail else ''
                    s = f'{tail}call {instr.receiver.name}({", ".join(str_value(arg) for arg in instr.args)})'
                case ArithmeticOp() | LogicOp() | ShiftOp() | CompareOp():
                    s = f'{str_value(instr.x)} {instr.op} {str_value(instr.y)}'
                case NegateOp():
                    s = f'neg {str_value(instr.x)}'
                case Convert():
                    s = f'convert {str_value(instr.value)} to {instr.type}'
                case IfOp():
                    s = f'if {str_value(instr.x)} {instr.cond} {str_value(instr.y)} then {str_value(instr.tval)} else {str_value(instr.fval)}'
                case If():
                    s = f'if {str_value(instr.x)} {instr.cond} {str_value(instr.y)} then goto B{instr.sux[0].block_id} else B{instr.sux[1].block_id}'
                case NewArray():
                    s = f'new_array {str_value(instr.size)} {str_value(instr.init)}'
                case NewTuple():
                    s = f'new_tuple ({", ".join(str_value(elem) for elem in instr.elems)})'
                case ReadFloat():
                    s = 'read_float'
                case ReadInt():
                    s = 'read_int'
                case PrintByte():
                    s = f'print_byte {str_value(instr.arg)}'
                case PrintInt():
                    s = f'print_int {str_value(instr.arg)}'
                case FloatPrimitive():
                    s = f'{instr.name} {str_value(instr.arg)}'
                case Return() as r:
                    if r.value is None:
                        s = 'return'
                    else:
                        s = f'return {str_value(r.value)}'
                case _:
                    s = str(instr)
            file.write(s)
            file.write('\n')
        file.write('\n')
    
    def print_function(self, f: Function, bbs: Mapping[int, BlockBegin], /, file: TextIOWrapper):
        assert next(iter(bbs.items()))[1] is f.entry
        print(f'Function {f.name if not f.name.is_main() else "main"}: return type {f.ret_type}', file=file)
        if f.formal_args:
            print('Formal arguments:', file=file)
            for local in f.formal_args:
                assert local.type is not None
                print(f'    {str_value(local, True)} {str(local.name):>10}, offset {local.offset:5}, size {local.type.abi_size:5} word(s)', file=file)
        if f.load_fv_fields:
            raise NotImplementedError()
        print(f'Blocks: total {len(bbs)}', file=file)
        for b in bbs.values():
            self.print_block(b, file=file)


class GraphVerifier:
    def compute_dominators(self, f: Function, /):
        blocks = f.collect_all_blocks()
        in_ = {b: set[int]() for b in blocks}
        out_ = {b: set(blocks) for b in blocks}
        out_[f.entry.block_id] = {f.entry.block_id}
        del blocks[f.entry.block_id]
        changed = True
        while changed:
            changed = False
            for b, block in blocks.items():
                i, o = in_[b], out_[b]
                i.clear()
                if block.predesessors:
                    i |= out_[block.predesessors[0].block_id]
                for p in block.predesessors[1:]:
                    i &= out_[p.block_id]
                out_old = o.copy()
                o.clear()
                o |= i
                o.add(b)
                if out_old != o:
                    changed = True
        return out_
    def verify_block_fast(self, b: BlockBegin, /):
        assert b.end is not None
        assert isinstance(b.end, BlockEnd)
        assert all(b in p.end.sux for p in b.predesessors)
        assert all(b in sux.predesessors for sux in b.end.sux)

    def verify(self, f: Function, /):
        from collections import deque
        b = f.entry
        assert b.is_entry
        q = deque([b])
        visited = {b.block_id: b}
        while q:
            b = q.popleft()
            for s in b.end.sux:
                assert isinstance(s, BlockBegin)
                if s.block_id not in visited:
                    assert not s.is_entry
                    visited[s.block_id] = s
                    q.append(s)

        for b in visited.values():
            self.verify_block_fast(b)
        dominators = self.compute_dominators(f)
        visited2 = {f.entry.block_id}
        GraphVerifier.collect_use_count(f)
        self.verify_block(f.entry, None, dominators, visited2, ChainMap({}, {local.id: local for local in f.formal_args}))
        assert visited.keys() == visited2

    @staticmethod
    def clear_use_count(f: Function, blocks: dict[int, BlockBegin] | None = None, /):
        if blocks is None:
            blocks = f.collect_all_blocks()
        for b in blocks.values():
            for i in GraphPrinter.get_instrs(b):
                i.use_count = 0
    
    @staticmethod
    def collect_use_count(f: Function, blocks: dict[int, BlockBegin] | None = None, /):
        if blocks is None:
            blocks = f.collect_all_blocks() 
        GraphVerifier.clear_use_count(f, blocks)
        for b in blocks.values():
            for i in GraphPrinter.get_instrs(b):
                for v in i.input_values():
                    v.use_count += 1
    
    def verify_block(self, b: BlockBegin, prev: BlockBegin | None, dominators: dict[int, set[int]], visited: set[int], env: ChainMap[int, Value], /):
        assert b.block_id in visited
        assert (len(b.end.sux) == 0) == isinstance(b.end, Return)
        instrs: list[Value] = []
        dom = dominators[b.block_id]
        i: Value = b
        while i.next is not None:
            assert not isinstance(i, BlockEnd)
            instrs.append(i.next)
            i = i.next
        else:
            assert isinstance(i, BlockEnd)
        phis: list[Phi] = []
        j = 0
        while j < len(instrs) and isinstance(i:=instrs[j], Phi):
            phis.append(i)
            j += 1
        assert all(not isinstance(instrs[j], Phi) for j in range(len(phis), len(instrs)))

        if len(phis) > 0:
            assert not b.is_entry
            assert prev is not None and prev in b.predesessors
            for phi in phis:
                assert phi.type is not None
                assert len(phi.preds) == len(b.predesessors)
                for v, p in zip(phi.preds, b.predesessors):
                    assert v.type is not None and phi.type == v.type.base()
                    if p is prev:
                        assert v.id in env
                        assert env[v.id] is v
                    elif v not in phis:
                        assert (v.id in env) == (v.block.block_id in dom)

            for phi in phis:
                env[phi.id] = phi

        for j in range(len(phis), len(instrs)):
            i = instrs[j]
            assert not isinstance(i, Phi)
            for v in i.input_values():
                assert v.id in env and env[v.id] is v
            assert i.id not in env
            if i.type is not None:
                env[i.id] = i
        
        for sux in b.end.sux:
            if sux.block_id not in visited:
                visited.add(sux.block_id)
                self.verify_block(sux, b, dominators, visited, env.new_child())
    
    def has_critical_edge(self, f: Function, /):
        blocks = f.collect_all_blocks()
        for b in blocks.values():
            if len(b.end.sux) > 1:
                for sux in b.end.sux:
                    if len(sux.predesessors) > 1:
                        return True
        return False

class GraphOptimizer:
    def remove_indirect_jumps(self, b: BlockBegin, visited: set[int], /):
        if b.block_id in visited:
            return
        visited.add(b.block_id)
        if b.end.sux:
            for s in b.end.sux:
                self.remove_indirect_jumps(s, visited)
        else:
            return
        for i in range(len(b.end.sux)):
            nb = b.end.sux[i]
            if isinstance(nb.next, Goto):
                nnb = nb.end.sux[0]
                if not isinstance(nnb.next, Phi):
                    if len(b.end.sux) > 1 and len(nnb.predesessors) > 1:
                        logger.info(f"remove {nb} in the indirect jump: {b} -> {nb} -> {nnb} would create a critical edge, so don't remove it")
                        continue
                    nnb.predesessors.append(b)
                    b.end.sux[i] = nnb
                    nb.predesessors.remove(b)
                    if not nb.predesessors:
                        logger.info(f'removed dead block: {nb}')
                        nnb.predesessors.remove(nb)
                    
                    logger.info(f'removed indirect jump: {b} -> {nb} -> {nnb} to {b} -> {nnb}')

    def remove_unused_values(self, f: Function, /):
        blocks = f.collect_all_blocks()
        changed = True
        while changed:
            changed = False
            GraphVerifier.collect_use_count(f, blocks)
            for b in blocks.values():
                i: Value = b
                while i.next is not None:
                    if i.next.use_count == 0 and isinstance(i.next, (ArithmeticOp, CompareOp, LogicOp, ShiftOp, NegateOp, Convert, IfOp, LoadField, NewArray, NewTuple, Constant, Local, Phi, FloatPrimitive)):
                        assert i.next.next is not None
                        i.next = i.next.next
                        changed = True
                    else:
                        i = i.next

    def split_critical_edges(self, f: Function, /):
        blocks = f.collect_all_blocks()
        for b in blocks.values():
            if len(b.end.sux) > 1:
                for sux in b.end.sux:
                    if len(sux.predesessors) > 1:
                        new_block = BlockBegin()
                        new_block.next = new_block.end = Goto(sux, new_block)
                        new_block.predesessors.append(b)
                        for i in range(len(b.end.sux)):
                            if b.end.sux[i] is sux:
                                b.end.sux[i] = new_block
                        for i in range(len(sux.predesessors)):
                            if sux.predesessors[i] is b:
                                sux.predesessors[i] = new_block
                        logger.info(f'split critical edge: {b} -> {sux} to {b} -> {new_block} -> {sux}')

    def loop_transformation(self, f: Function, /):
        def collect_values(b: BlockBegin, /):
            values: list[Value] = [b]
            i: Value = b
            while i.next is not None:
                values.append(i.next)
                i = i.next
            return values
        def preds_all_same(vs: Iterable[Value], /):
            return len(set(v.id for v in vs)) == 1

        def mask(vs: Sequence[Value], m: Sequence[bool], /):
            return [v for v, b in zip(vs, m) if not b]
        
        blocks = f.collect_all_blocks()
        worklist: list[tuple[BlockBegin, Value, list[Value]]] = []
        for block in blocks.values():
            values = collect_values(block)
            assert len(values) >= 2 and isinstance(values[0], BlockBegin) and isinstance(values[-1], BlockEnd)
            # obviously, len(values) >= 2 (blockBegin and blockEnd)
            for i in range(1, len(values)):
                value = values[i]
                if isinstance(value, InvokeStatic) and value.receiver is f and value.tail:
                    assert isinstance(value.next, Return)
                    assert value.use_count <= 1
                    worklist.append((block, values[i-1], value.args))
        if worklist:
            logger.info(f'in function {f.name}, worklist: {worklist}')
            old_entry = f.entry
            f.entry = f.entry.split_entry()
            assert not old_entry.is_entry
            assert len(old_entry.predesessors) == 1
            predss: list[list[Value]] = [list(f.formal_args)] # preds[:, i] is all the ith arguments of the tail calls
            for block, tailcall_prev, args in worklist:
                tailcall_prev.next = block.end = Goto(old_entry, block)
                old_entry.predesessors.append(block)
                predss.append(args)
            assert not isinstance(old_entry.next, Phi)
            # is_preds_all_same = [preds_all_same(vs) for vs in zip(*predss)]
            # if not all(is_preds_all_same):
                # no_same_preds_args = [arg for i, arg in enumerate(f.formal_args) if not is_preds_all_same[i]]
            types = [arg.type for arg in f.formal_args if arg.type is not None]

            # assert len(types) + sum(is_preds_all_same, 0) == len(f.formal_args)
            # predss = [mask(vs, is_preds_all_same) for vs in predss]
            phis: list[Phi] = [Phi(type, [predss[i][j] for i in range(len(predss))], old_entry) for j, type in enumerate(types)]
            assert old_entry.next is not None

            # replace the tail call arguments with the phis e.g. f(x, y) tail calls f(y, x) then we have phi1 = [x, phi2] and phi2 = [y, phi1]
            for phi in phis:
                for i in range(1, len(phi.preds)):
                    if phi.preds[i] in f.formal_args:
                        phi.preds[i] = phis[f.formal_args.index(phi.preds[i])]

            for block in blocks.values():
                for instr in collect_values(block):
                    for v in instr.input_values():
                        if v in f.formal_args:
                            instr.replace_uses(v, phis[f.formal_args.index(v)])
            phis[-1].next = old_entry.next
            old_entry.next = phis[0]
            for i in range(1, len(phis)):
                phis[i-1].next = phis[i]
                
