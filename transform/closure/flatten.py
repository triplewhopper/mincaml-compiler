from withbounds import WithBounds
from bounds import Bounds
from transform.knormal import BinaryOpKind, UnaryOpKind
from .language import Exp, Lit, Var, Get, Unary, AppDir, AppCls, Binary, Seq, Tuple, Put, If, Let, LetTuple, \
    MakeCls, Function, Cls, LetBinding
from id import Id # , Id, Id, tmp_id_factory
from ty import Ty, TyFun, TyTuple, TyUnit, TyArray, TyInt, TyFloat, TyBool
# from .visitor import ExpVisitor
from .emit import IREmitter as LLVMIREmitter, partition
from .. import bind_logger
import llvmlite.ir as ir
import transform.virtual.virtual as V
import logging
from collections import ChainMap
from collections.abc import Iterable
from typing import Callable

get_adapter = bind_logger(logger=logging.getLogger(__name__))


def prune(t: Ty) -> Ty:
    match t:
        case TyUnit() | TyInt() | TyFloat() | TyBool() | TyArray(TyUnit() | TyInt() | TyFloat() | TyBool()):
            return t
        case TyArray(e):
            e1 = prune(e)
            if e is e1:
                return t
            return TyArray(e1)
        case TyTuple(elems):
            elems1 = tuple(e1 for e1 in map(prune, elems) if e1 is not TyUnit())
            if elems == elems1:
                return t
            if len(elems1) == 1:
                return elems1[0]
            return TyTuple(elems1)
        case TyFun(args, ret):
            args1 = tuple(e1 for e1 in map(prune, args) if e1 is not TyUnit())
            ret1 = prune(ret)
            if ret is ret1 and args == args1:
                return t
            return TyFun(*args1, ret1)
        case _:
            raise NotImplementedError()


class Flatten:
    def get_fn_decl(self, fns: set[Id], ml_ty: TyFun) -> dict[Id, V.Function]:
        declared: dict[str, V.Function] = {}
        ans: dict[Id, V.Function] = {}
        ir_ext_fn_ty = ir.FunctionType(LLVMIREmitter.get_ir_ty(ml_ty.ret), LLVMIREmitter.get_ir_tys(ml_ty.args))
        assert isinstance(ir_ext_fn_ty, ir.FunctionType)
        for fn in fns:
            name = fn.val.val
            # if name in ('Array.make', 'Array.create'):
            #     name = f"create.array"
            if name not in declared:
                # if name == 'create.array':
                # assert len(ir_ext_fn_ty.args) == 2
                # args = [V.Argument(ir_ext_fn_ty.args[0], Flatten.suffix(fn, f"num")),
                #         V.Argument(ir.IntType(32), Flatten.suffix(fn, "size"))]
                # ir_ext_fn_ty2 = ir.FunctionType(ir.IntType(8).as_pointer(), [ir.IntType(32), ir.IntType(32)], var_arg=True)
                # ir_fn_decl = V.Function(fn, ir_ext_fn_ty2, tuple(args), ())
                # with get_adapter(fn.bounds) as adapter:
                #     adapter.info(
                #         f"Creating external function declaration {ir_fn_decl.funct.dump()} of type '{ir_fn_decl.ftype}'")
                # else:
                n_args = len(ir_ext_fn_ty.args)
                ir_fn_decl = V.Function(
                    fn, ir_ext_fn_ty, tuple(fn.suffix(f"arg.{i}") for i in range(n_args)), ())
                with get_adapter(fn.bounds) as adapter:
                    adapter.info(
                        f"Creating external function declaration {ir_fn_decl.funct.dump()} of type '{ir_fn_decl.ftype}'")

                ans[fn] = ir_fn_decl
                declared[name] = ir_fn_decl
            else:
                ans[fn] = declared[name]
        return ans

    def get_ext_var_decl(self, ext_vars: set[Id], ml_ext_ty: TyArray | TyTuple) \
            -> dict[Id, V.GlobalVariable]:
        assert isinstance(ml_ext_ty, (TyArray, TyTuple))
        declared: dict[str, V.GlobalVariable] = {}
        ans: dict[Id, V.GlobalVariable] = {}
        ir_ext_var_ty = LLVMIREmitter.get_ir_ty(ml_ext_ty)
        for ext_var in ext_vars:
            if ext_var.val.val not in declared:
                ir_ext_arr_decl = V.GlobalVariable(ir_ext_var_ty, ext_var)
                # ir_ext_arr_decl.unnamed_addr = True
                # ir_ext_arr_decl.global_constant = True
                with get_adapter(ext_var.bounds) as adapter:
                    adapter.info(
                        f"Creating external array declaration @{ir_ext_arr_decl.name} of type '{ir_ext_arr_decl.typ}'")
                ans[ext_var] = ir_ext_arr_decl
                declared[ext_var.val.val] = ir_ext_arr_decl
            else:
                ans[ext_var] = declared[ext_var.val.val]

        return ans

    def get_global_var_decl(self, global_vars: set[Id], ml_global_ty: Ty) \
            -> dict[Id, V.GlobalVariable]:
        if isinstance(ml_global_ty, TyFun):
            return {}
        declared: dict[str, V.GlobalVariable] = {}
        ans: dict[Id, V.GlobalVariable] = {}
        ir_global_var_ty = LLVMIREmitter.get_ir_ty(ml_global_ty)
        for global_var in global_vars:
            if global_var.val.val not in declared:
                ir_global_var_decl = V.GlobalVariable(ir_global_var_ty, global_var)
                # ir_global_var_decl.unnamed_addr = True
                # ir_global_var_decl.global_constant = True
                with get_adapter(global_var.bounds) as adapter:
                    adapter.info(
                        f"Creating global declaration @{ir_global_var_decl.name} of type '{ir_global_var_decl.typ}'")
                ans[global_var] = ir_global_var_decl
                declared[global_var.val.val] = ir_global_var_decl
            else:
                ans[global_var] = declared[global_var.val.val]

        return ans

    def get_local_fn_decl(self, ml_fn: Function) \
            -> tuple[ir.Function, Callable[[V.IRBuilder], dict[Id, V.HasRd | None]]]:

        non_void_arg_names, non_void_arg_types, void_arg_names = partition(ml_fn.iter_args())
        non_void_fv_names, non_void_fv_types, void_fv_names = partition(ml_fn.formal_fv)
        fn_ir_ret_ty = LLVMIREmitter.get_ir_ty(ml_fn.typ.ret)
        ml_fn_ir_ty = ir.FunctionType(fn_ir_ret_ty, non_void_arg_types)

        del non_void_arg_types, fn_ir_ret_ty
        ir_fn = V.Function(
            ml_fn.funct, ml_fn_ir_ty, tuple(non_void_arg_names), tuple(zip(non_void_fv_names, non_void_fv_types)))

        with get_adapter(ml_fn.bounds) as adapter:
            adapter.info(f"Creating local function declaration {ir_fn.funct.dump()} of type '{ir_fn.ftype}'")
            if len(non_void_fv_types) > 0:
                adapter.info(
                    f"function {ir_fn.funct.dump()} has an extra argument of type '{ir_fn.args[-1].typ}' for passing free variables")

        if len(non_void_fv_types) == 0:
            assert len(non_void_arg_names) == len(ir_fn.ftype.args)
        else:
            assert len(non_void_arg_names) + 1 == len(ir_fn.ftype.args)

        del ml_fn_ir_ty

        def get_fn_local_env(builder: V.IRBuilder):
            ir_fn_local_env: dict[Id, V.HasRd | None] = {void_arg_name: None for void_arg_name in void_arg_names}
            for arg in ir_fn.args:
                ir_fn_local_env[arg.rd] = arg

            ir_fn_local_env.update({void_fv_name: None for void_fv_name in void_fv_names})
            if len(non_void_fv_types) > 0:
                fv_struct = builder.append(V.Load(ir_fn.args[-1]))
                fv_struct.rd = builder.function.funct.suffix('fv.struct')
                for i, x in enumerate(non_void_fv_names):
                    instr = V.ExtractValue(fv_struct, i)
                    instr.rd = x.suffix('from.fv')
                    ir_fn_local_env[x] = builder.append(instr)

            return ir_fn_local_env

        return ir_fn, get_fn_local_env

    @staticmethod
    def create_main():
        m = WithBounds('main', Bounds('flatten.py', 1, 1, 1, 1))
        m = Id.create_definition(m)
        f = V.Function(m, ir.FunctionType(ir.IntType(32), []), (), ())
        return f

    def __init__(self):
        # self._global_offset_table: dict[Id | V.Label, Future[int]] = {}
        # self._global_offset_table_label = V.Label('global_offset_table')
        self._locals_stack: dict[Id, dict[Id, int]] = {}
        self._ty_env: dict[Id, ir.Type] = {}
        self._env: dict[Id, V.HasRd | V.GlobalVariable | None] = {}
        self._functions = ChainMap[Id, V.Function]()
        self._main = Flatten.create_main()
        self._builder = V.IRBuilder(self._main.emplace_basic_block())
        self._floats: list[float] = []
        self._frame: dict[Id, int] = {}

    def emit(self, ext_fns: dict[TyFun, set[Id]], global_varss: dict[Ty, set[Id]],
             ml_local_fns: list[Function], mains: list[Exp | Cls | LetBinding]):
        for global_var_ty, global_vars in global_varss.items():
            self._env.update(self.get_global_var_decl(global_vars, global_var_ty))

        for ext_fn_ty, ext_fns1 in ext_fns.items():
            self._functions.update(self.get_fn_decl(ext_fns1, ext_fn_ty))

        self._functions = self._functions.new_child()
        mk_local_fn_env: dict[Id, Callable[[V.IRBuilder], dict[Id, V.HasRd | None]]] = {}
        for ml_fn in ml_local_fns:
            assert ml_fn.funct not in self._functions, f"why function '{ml_fn.funct}' is already defined?"
            f, g = self.get_local_fn_decl(ml_fn)
            self._functions[ml_fn.funct] = f
            mk_local_fn_env[ml_fn.funct] = g
        # initialization for global functions
        assert len(ml_local_fns) == len(self._functions.maps[0])

        for ml_fn, ir_fn in zip(ml_local_fns, self._functions.maps[0].values()):
            assert len(self._functions.maps[0]) == len(ml_local_fns)
            self._builder = V.IRBuilder(ir_fn.emplace_basic_block())
            local_fn_env = mk_local_fn_env[ml_fn.funct](self._builder)
            for k, v in local_fn_env.items():
                assert k not in self._env
                self._env[k] = v

            r = self.visit(ml_fn.body)
            assert (r is None) == isinstance(ir_fn.ftype.return_type, ir.VoidType)
            if r is not None:
                if isinstance(r, V.HasRd):
                    r.rd = r.rd.suffix('return')
                self._builder.append(V.Ret(r))
            else:
                self._builder.append(V.RetVoid())

            for k in local_fn_env:
                del self._env[k]

        self._builder = V.IRBuilder(self._main.emplace_basic_block())
        assert len(self._env) == sum(len(v) for k, v in global_varss.items() if not isinstance(k, TyFun))
        assert len(self._functions.maps) == 2 and len(self._functions.maps[0]) == len(ml_local_fns)
        for main in mains:
            if isinstance(main, Exp):
                if isinstance((r := self.visit(main)), V.HasRd):
                    r.rd = r.rd.suffix('unused')
            elif isinstance(main, Cls):
                raise NotImplementedError()
            else:
                rhs_val = self.visit(main.rhs)
                if isinstance(rhs_val, V.HasRd):
                    rhs_val.rd = main.lhs
                self._env[main.lhs] = rhs_val

        self._builder.append(V.Ret(V.Imm(0)))

    def dump(self, f):
        printed = set()
        for fun in self._functions.values():
            if id(fun) not in printed:
                fun.optimize()
                print(fun, file=f)
                # if fun.n_blocks > 0:
                #     fun.draw_cfg()
                printed.add(id(fun))
        self._main.optimize()
        print(self._main, file=f)

        self._main.draw_cfg()

    def lookup(self, key: Id):
        try:
            v = self._env[key]
        except KeyError:
            v = self._functions[key]
        if isinstance(v, V.GlobalVariable):
            return self._builder.append(V.Load(v))
        return v

    def lookups(self, keys: Iterable[Id]):
        for key in keys:
            v = self.lookup(key)
            if v is not None:
                yield v

    def visit(self, node: Exp) -> V.HasRd | None:
        v = getattr(self, f"visit_{type(node).__name__}")(node)
        assert (v is None) == (V.get_abi_size(node.typ) == 0)
        return v

    def visit_Lit(self, node: Lit) -> V.Imm | None:
        match node.lit.val:
            case bool() | int() | float() as v:
                return V.Imm(v)

        assert node.lit.val == '()'

    def visit_Var(self, node: Var):
        return self.lookup(node.name)

    # def visit_Ext(self, node: Ext):
    #     assert node.typ is not TyUnit()
    #     res = self._env[node.name]
    #     assert isinstance(res, V.Function)
    #     return res

    def visit_Get(self, node: Get):
        arr = self.lookup(node.array)
        idx = self.lookup(node.index)
        gep = self._builder.append(V.GetElementPtr(arr, idx))
        return self._builder.append(V.Load(gep))

    def visit_Unary(self, node: Unary):
        match node.op.val:
            case UnaryOpKind.I_NEG:
                return self._builder.append(V.Neg(self._env[node.y]))
            case UnaryOpKind.F_NEG:
                return self._builder.append(V.FNeg(self._env[node.y]))
            case _:
                raise NotImplementedError(node.op.val)

    def visit_AppCls(self, node: AppCls, /):
        callee = self.lookup(node.callee)
        args = list(self.lookups(node.args))
        if self._builder.function is callee:
            assert isinstance(callee, V.Function)
            assert len(self._builder.function.formal_fv) > 0
            v = self._builder.append(callee(*args, self._builder.function.args[-1]))
            if not isinstance(v.typ, ir.VoidType):
                return v
        else:
            entry_ptr = self._builder.append(V.ExtractValue(callee, 0))
            fv_ptr = self._builder.append(V.ExtractValue(callee, 1))
            cond = self._builder.append(V.Eq(fv_ptr, V.Imm(0, fv_ptr.typ)))

            with self._builder.if_else(cond) as (then, otherwise):
                with then:
                    entry_ptr1 = self._builder.append(V.BitCast(entry_ptr, V.cls_ptr_to_func_ptr(entry_ptr.typ)))
                    v1 = self._builder.append(entry_ptr1(*args))
                    b1 = self._builder.block
                with otherwise:
                    v2 = self._builder.append(entry_ptr(*args, fv_ptr))
                    b2 = self._builder.block
            assert (v1 is None) == (v2 is None)
            if v1 is None:
                return None
            assert v2 is not None and v1.typ == v2.typ == entry_ptr.typ.pointee.return_type
            if not isinstance(v1.typ, ir.VoidType):
                phi = self._builder.append(V.Phi(v1.typ))
                phi.add_incoming(v1, b1)
                phi.add_incoming(v2, b2)
                return phi
        return None

    def visit_AppDir(self, node: AppDir):
        callee = self._functions[node.callee]
        args = list(self.lookups(node.args))
        v = self._builder.append(callee(*args))
        if not isinstance(v.typ, ir.VoidType):
            return v
        return None

    def visit_Binary(self, node: Binary, /):
        x = self._env[node.y1]
        y = self._env[node.y2]
        assert x is not None and y is not None
        match node.op.val:
            case BinaryOpKind.I_ADD:
                return self._builder.append(V.Add(x, y))
            case BinaryOpKind.I_SUB:
                return self._builder.append(V.Sub(x, y))
            case BinaryOpKind.I_MUL:
                return self._builder.append(V.Mul(x, y))
            case BinaryOpKind.I_DIV:
                return self._builder.append(V.Div(x, y))
            case BinaryOpKind.F_ADD:
                return self._builder.append(V.FAdd(x, y))
            case BinaryOpKind.F_SUB:
                return self._builder.append(V.FSub(x, y))
            case BinaryOpKind.F_MUL:
                return self._builder.append(V.FMul(x, y))
            case BinaryOpKind.F_DIV:
                return self._builder.append(V.FDiv(x, y))
            case BinaryOpKind.I_EQ | BinaryOpKind.B_EQ:
                return self._builder.append(V.Eq(x, y))
            case BinaryOpKind.I_NEQ | BinaryOpKind.B_NEQ:
                return self._builder.append(V.Neq(x, y))
            case BinaryOpKind.I_LE:
                return self._builder.append(V.Sle(x, y))
            case BinaryOpKind.I_GE:
                return self._builder.append(V.Sge(x, y))
            case BinaryOpKind.I_LT:
                return self._builder.append(V.Slt(x, y))
            case BinaryOpKind.I_GT:
                return self._builder.append(V.Sgt(x, y))
            case BinaryOpKind.F_EQ:
                return self._builder.append(V.Oeq(x, y))
            case BinaryOpKind.F_NEQ:
                return self._builder.append(V.One(x, y))
            case BinaryOpKind.F_LE:
                return self._builder.append(V.Ole(x, y))
            case BinaryOpKind.F_GE:
                return self._builder.append(V.Oge(x, y))
            case BinaryOpKind.F_LT:
                return self._builder.append(V.Olt(x, y))
            case BinaryOpKind.F_GT:
                return self._builder.append(V.Ogt(x, y))
            case x:
                raise NotImplementedError(x)

    def visit_Seq(self, node: Seq, /):
        r = None
        for e in node.es:
            r = self.visit(e)
        return r

    def visit_Tuple(self, node: Tuple, /):
        tup_ty = LLVMIREmitter.get_ir_ty(node.typ)
        if isinstance(tup_ty, ir.VoidType):
            return None
        vs = list(self.lookups(node.ys))
        if all(isinstance(v, V.Imm) for v in vs):
            return vs
        if isinstance(tup_ty, ir.LiteralStructType):
            assert len(vs) >= 2
            tup_ptr = self._builder.append(V.Alloca(tup_ty))
            tup = self._builder.append(V.Load(tup_ptr))
            for i, v in enumerate(vs):
                tup = self._builder.append(V.InsertValue(tup, v, i))
            return tup

        else:
            assert len(vs) == 1
            return vs[0]

    def visit_Put(self, node: Put, /):
        arr = self.lookup(node.array)
        idx = self._env[node.index]
        val = self.lookup(node.value)
        gep = self._builder.append(V.GetElementPtr(arr, idx))
        self._builder.append(V.Store(val or V.Imm(0), gep))

    def visit_If(self, node: If, /):
        cond = self._env[node.cond]
        b = self._builder.block
        with self._builder.if_else(cond) as (then, otherwise):
            with then:
                v1 = self.visit(node.br_true)
                b1 = self._builder.block
            with otherwise:
                v2 = self.visit(node.br_false)
                b2 = self._builder.block
        assert (v1 is None) == (v2 is None)
        if v1 is None:
            return None
        assert v2 is not None and v1.typ == v2.typ
        phi = self._builder.append(V.Phi(v1.typ))
        phi.add_incoming(v1, b1)
        phi.add_incoming(v2, b2)
        return phi

    def visit_Let(self, node: Let):
        rhs_val = self.visit(node.binding.rhs)
        assert (rhs_val is None) == (V.get_abi_size(node.binding.rhs.typ) == 0)
        assert node.binding.lhs not in self._env
        if rhs_val is not None:
            if isinstance(rhs_val, V.HasRd):
                rhs_val.rd = node.binding.lhs
            self._env[node.binding.lhs] = rhs_val
        else:
            self._env[node.binding.lhs] = None
        res = self.visit(node.expr)
        del self._env[node.binding.lhs]
        return res

    def visit_LetTuple(self, node: LetTuple, /):
        y = self._env[node.y]
        assert all(x not in self._env for x in node.xs)
        if y is None:
            self._env.update({x: None for x in node.xs})
        else:
            non_void_xs, non_void_ts, void_xs = partition(zip(node.xs, node.ts))
            self._env.update({void_x: None for void_x in void_xs})
            if len(non_void_xs) == 1:
                self._env[non_void_xs[0]] = y
            else:
                for i, non_void_x in enumerate(non_void_xs):
                    self._env[non_void_x] = self._builder.append(V.ExtractValue(y, i, rd=non_void_x))
        res = self.visit(node.e)
        for x in node.xs:
            del self._env[x]
        return res

    def visit_MakeCls(self, node: MakeCls, /):
        cls_entry_func = self._functions[node.closure.entry.funct]
        i8_ptr_ty = V.i8.as_pointer()
        if len(cls_entry_func.formal_fv):
            actual_fv = list(self.lookups(fv for fv, _ in cls_entry_func.formal_fv))
            assert all(fv is not None for fv in actual_fv)
            actual_fv_prefix = cls_entry_func.funct.suffix('fv')
            fv_struct_ty = cls_entry_func.fv_struct_ptr_typ.pointee
            actual_fv_struct_ptr_calloc = self._builder.append(V.Calloc(V.Imm(1), V.Imm(V.get_abi_size(fv_struct_ty))))
            actual_fv_struct_ptr = self._builder.append(
                V.BitCast(actual_fv_struct_ptr_calloc, fv_struct_ty.as_pointer()))
            actual_fv_struct_ptr.rd = actual_fv_prefix.suffix('struct.ptr')
            actual_fv = list(self.lookups(node.closure.actual_fv))
            assert len(actual_fv) == len(cls_entry_func.formal_fv)
            for i, fv in enumerate(actual_fv):
                gep = self._builder.append(V.GetElementPtr(actual_fv_struct_ptr, V.Imm(0), V.Imm(i)))
                gep.rd = actual_fv_struct_ptr.rd.suffix(f"elem.{i}.ptr")
                self._builder.append(V.Store(fv, gep))
            cls_entry_downcast = self._builder.append(
                V.BitCast(cls_entry_func, cls_entry_func.typ_as_closure_entry_erased.as_pointer()))
            cls_entry_downcast.rd = cls_entry_func.funct.suffix('downcast')
            actual_fv_struct_ptr_downcast = self._builder.append(V.BitCast(actual_fv_struct_ptr, i8_ptr_ty))
            actual_fv_struct_ptr_downcast.rd = actual_fv_struct_ptr.rd.suffix('downcast')
            cls_ptr = self._builder.append(V.Alloca(ir.LiteralStructType([cls_entry_downcast.typ, i8_ptr_ty])))
            cls_ptr.rd = cls_entry_func.funct.suffix('closure.ptr')
            cls_entry_ptr = self._builder.append(V.GetElementPtr(cls_ptr, V.Imm(0), V.Imm(0)))
            cls_entry_ptr.rd = cls_entry_func.funct.suffix('closure.entry.ptr')
            self._builder.append(V.Store(cls_entry_downcast, cls_entry_ptr))
            fv_ptr = self._builder.append(V.GetElementPtr(cls_ptr, V.Imm(0), V.Imm(1)))
            fv_ptr.rd = cls_entry_func.funct.suffix('closure.fv.ptr')
            self._builder.append(V.Store(actual_fv_struct_ptr_downcast, fv_ptr))
            cls = self._builder.append(V.Load(cls_ptr))
            cls.rd = cls_entry_func.funct.suffix('closure')

        else:
            cls_entry_ty_lift = cls_entry_func.typ_lift_to_closure_entry
            cls_entry_lift = V.BitCast(cls_entry_func, cls_entry_ty_lift.as_pointer())
            cls_entry_lift.rd = cls_entry_func.funct.suffix('as.ptr.lifted')
            cls_ptr = self._builder.append(V.Alloca(ir.LiteralStructType([cls_entry_lift.typ, i8_ptr_ty])))
            cls_ptr.rd = cls_entry_func.funct.suffix('closure.ptr')
            cls_entry_ptr = self._builder.append(V.GetElementPtr(cls_ptr, V.Imm(0), V.Imm(0)))
            cls_entry_ptr.rd = cls_entry_func.funct.suffix('closure.entry.ptr')
            self._builder.append(V.Store(cls_entry_lift, cls_entry_ptr))
            cls_fv_ptr = self._builder.append(V.GetElementPtr(cls_ptr, V.Imm(0), V.Imm(1)))
            cls_fv_ptr.rd = cls_entry_func.funct.suffix('closure.fv.ptr')
            self._builder.append(V.Store(V.Imm(0, i8_ptr_ty), cls_fv_ptr))
            cls = self._builder.append(V.Load(cls_ptr, rd=cls_entry_func.funct.suffix('closure')))
        assert node.closure.entry.funct not in self._env
        self._env[node.closure.entry.funct] = cls
        v = self.visit(node.body)
        del self._env[node.closure.entry.funct]
        return v
