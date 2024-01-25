import contextlib
import logging
from collections.abc import Iterable, Callable
import llvmlite.ir as ir
import llvmlite.binding as binding
import id
import transform.knormal as kn
from . import language as cl
# from .visitor import ExpVisitor
from collections import ChainMap
from functools import lru_cache
import ty

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

x64_layout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
x64_triple = "x86_64-apple-macosx13.0.0"
rv32_layout = "e-m:e-p:32:32-i64:64-n32-S128"
rv32_triple = "riscv32-unknown-unknown"
target_data = binding.create_target_data(rv32_layout)


def partition(xts: Iterable[tuple[id.Id, ty.Ty]]) -> \
        tuple[list[id.Id], list[ir.Type], list[id.Id]]:
    y1s, y2s, ns = [], [], []
    for x, t in xts:
        t = IREmitter.get_ir_ty(t)
        if isinstance(t, ir.VoidType):
            ns.append(x)
        else:
            y1s.append(x)
            y2s.append(t)
    return y1s, y2s, ns


class IREmitter:

    @staticmethod
    @lru_cache(maxsize=128)
    def get_ir_ty(typ: ty.Ty) -> ir.Type:
        match typ:
            case ty.TyUnit():
                return ir.VoidType()
            case ty.TyInt():
                return ir.IntType(32)
            case ty.TyFloat():
                return ir.FloatType()
            case ty.TyBool():
                return ir.IntType(1)
            case ty.TyTuple(elems):
                elems = [e for e in map(IREmitter.get_ir_ty, elems) if not isinstance(e, ir.VoidType)]
                if not elems:
                    ir_ty = ir.VoidType()
                elif len(elems) == 1:
                    ir_ty = elems[0]
                else:
                    ir_ty = ir.LiteralStructType(elems)
                logger.info(f"min-caml type '{typ}' maps to LLVM type '{ir_ty}'")
                return ir_ty
            case ty.TyArray(ty.TyUnit()):
                ir_ty = ir.IntType(8).as_pointer()
                logger.info(f"min-caml type '{typ}' maps to LLVM type '{ir_ty}'")
                return ir_ty
            case ty.TyArray(elem):
                ir_ty = IREmitter.get_ir_ty(elem).as_pointer()
                logger.info(f"min-caml type '{typ}' maps to LLVM type '{ir_ty}'")
                return ir_ty
            case ty.TyFun(args, ret):
                args_ir_ty = [t for t in map(IREmitter.get_ir_ty, args) if not isinstance(t, ir.VoidType)]
                ir_ty = ir.FunctionType(IREmitter.get_ir_ty(ret), [*args_ir_ty, ir.IntType(8).as_pointer()])
                ir_ty = ir.LiteralStructType([ir_ty.as_pointer(), ir.IntType(8).as_pointer()])
                logger.info(f"min-caml type '{typ}' maps to LLVM type '{ir_ty}'")
                return ir_ty

    @staticmethod
    def get_ir_tys(typs: Iterable[ty.Ty], /, filter_out_void=True) -> list[ir.Type]:
        if filter_out_void:
            return [t for t in map(IREmitter.get_ir_ty, typs) if not isinstance(t, ir.VoidType)]
        else:
            return [IREmitter.get_ir_ty(t) for t in typs]

    def get_fn_decl(self, fns: set[id.Id], ml_ty: ty.TyFun) -> dict[id.Id, ir.Function]:
        declared: dict[str, ir.Function] = {}
        ans: dict[id.GlobalId, ir.Function] = {}
        ir_ext_fn_ty = ir.FunctionType(IREmitter.get_ir_ty(ml_ty.ret), IREmitter.get_ir_tys(ml_ty.args))
        assert isinstance(ir_ext_fn_ty, ir.FunctionType)
        for fn in fns:
            name = fn.val.val
            # if name in ('Array.make', 'Array.create'):
            #     name = f"create_array_{str(ml_ty.args[1]).strip().replace(' ', '_').replace('array', 'A')}"
            if name not in declared:
                ir_fn_decl = ir.Function(module=self.module, ftype=ir_ext_fn_ty, name='min_caml_' + name)
                logger.info(f"Creating external function declaration @{ir_fn_decl.name} of type '{ir_fn_decl.type}'")

                for i, arg in enumerate(ir_fn_decl.args):
                    arg.add_attribute('noundef')
                    # arg.name = f"arg{i}"
                if name == 'not':
                    ir_fn_decl.attributes.add('alwaysinline')
                    ir_builder = ir.IRBuilder(ir_fn_decl.append_basic_block(name="entry"))
                    ir_builder.ret(ir_builder.not_(ir_fn_decl.args[0]))
                elif name == 'abs_float':
                    ir_fn_decl.attributes.add('alwaysinline')
                    ir_builder = ir.IRBuilder(ir_fn_decl.append_basic_block(name="entry"))
                    ge_zero = ir_builder.fcmp_ordered('>=', ir_fn_decl.args[0], ir_fn_decl.args[0].type(0.0))
                    neg = ir_builder.fneg(ir_fn_decl.args[0])
                    ir_builder.ret(ir_builder.select(ge_zero, ir_fn_decl.args[0], neg))
                ir_fn_decl.global_constant = True
                # ir_decl.initializer = ir.Constant(ty, None)
                ir_fn_decl.unnamed_addr = True
                ans[fn] = ir_fn_decl
                declared[name] = ir_fn_decl
            else:
                ans[fn] = declared[name]
        return ans

    def get_local_fn_decl(self, ml_fn: cl.Function) -> \
            tuple[ir.Function, Callable[[ir.IRBuilder], dict[id.Id, ir.NamedValue | None]]]:

        non_void_arg_names, non_void_arg_types, void_arg_names = partition(ml_fn.iter_args())
        non_void_fv_names, non_void_fv_types, void_fv_names = partition(ml_fn.formal_fv)
        fn_ir_ret_ty = IREmitter.get_ir_ty(ml_fn.typ.ret)
        if len(non_void_fv_types) > 0:
            fv_struct_ptr_ty = ir.LiteralStructType(non_void_fv_types).as_pointer()
            ml_fn_ir_ty = ir.FunctionType(fn_ir_ret_ty, [*non_void_arg_types, fv_struct_ptr_ty])
        else:
            fv_struct_ptr_ty = None
            ml_fn_ir_ty = ir.FunctionType(fn_ir_ret_ty, non_void_arg_types)

        del non_void_arg_types, fn_ir_ret_ty
        try:
            ir_fn = ir.Function(self.module, ml_fn_ir_ty, name=str(ml_fn.funct))
        except NameError:
            ir_fn = ir.Function(self.module, ml_fn_ir_ty, name=repr(ml_fn.funct))

        # ir_fn.calling_convention = 'tailcc'
        ir_fn.append_basic_block(name="entry")
        logger.info(f"Creating local function declaration @{ir_fn.name} of type '{ir_fn.ftype}'")
        if fv_struct_ptr_ty is not None:
            logger.info(
                f"function @{ir_fn.name} has an extra argument of type '{fv_struct_ptr_ty}' for passing free variables")

        for i in range(len(non_void_arg_names)):
            ir_fn.args[i].add_attribute('noundef')
            ir_fn.args[i].name = str(non_void_arg_names[i])

        if fv_struct_ptr_ty is None:
            assert len(non_void_arg_names) == len(ir_fn.args)
        else:
            assert len(non_void_arg_names) + 1 == len(ir_fn.args)
            ir_fn.args[-1].name = "fv.struct.ptr"
            ir_fn.args[-1].add_attribute('nonnull')
            ir_fn.args[-1].add_attribute('noundef')
        del ml_fn_ir_ty

        def get_fn_local_env(builder: ir.IRBuilder) -> dict[id.Id, ir.NamedValue | None]:
            ir_fn_local_env = {void_arg_name: None for void_arg_name in void_arg_names}
            for non_void_name, arg in zip(non_void_arg_names, ir_fn.args):
                ir_fn_local_env[non_void_name] = arg

            ir_fn_local_env.update({void_fv_name: None for void_fv_name in void_fv_names})
            if fv_struct_ptr_ty is not None:
                fv_struct = builder.load(ir_fn.args[-1], name=f"fv.struct")
                for i, x in enumerate(non_void_fv_names):
                    ir_fn_local_env[x] = builder.extract_value(fv_struct, i, name=f"fv.struct.{x}")

            return ir_fn_local_env

        return ir_fn, get_fn_local_env

    def get_ext_var_decl(self, ext_vars: set[id.Id], ml_ext_ty: ty.TyArray | ty.TyTuple) -> dict[
        id.Id, ir.GlobalVariable]:
        assert isinstance(ml_ext_ty, (ty.TyArray, ty.TyTuple))
        declared: dict[str, ir.GlobalVariable] = {}
        ans: dict[id.GlobalId, ir.GlobalVariable] = {}
        ir_ext_var_ty = IREmitter.get_ir_ty(ml_ext_ty)
        for ext_var in ext_vars:
            if ext_var.val.val not in declared:
                ir_ext_arr_decl = ir.GlobalVariable(module=self.module, typ=ir_ext_var_ty, name=ext_var.val.val)
                ir_ext_arr_decl.unnamed_addr = True
                ir_ext_arr_decl.global_constant = True
                logger.info(f"Creating external array @{ir_ext_arr_decl.name} of type '{ir_ext_arr_decl.type}'")
                ans[ext_var] = ir_ext_arr_decl
                declared[ext_var.val.val] = ir_ext_arr_decl
            else:
                ans[ext_var] = declared[ext_var.val.val]

        return ans

    def __init__(self):
        # module
        self.module = ir.Module(name=__file__)
        self.module.triple = rv32_triple
        self.module.data_layout = rv32_layout
        # functions
        ir_main_ty = ir.FunctionType(ir.IntType(32), [])
        self.ir_main = ir.Function(self.module, ir_main_ty, name='caml_main')
        logger.info(f"Creating function @{self.ir_main.name} with type '{ir_main_ty}'")
        self._env: ChainMap[id.Id, ir.NamedValue | None] = ChainMap()
        self._mk_local_fn_env: dict[id.Id, Callable[[ir.IRBuilder], dict[id.Id, ir.NamedValue | None]]] = {}
        self.builder = ir.IRBuilder(self.ir_main.append_basic_block(name="entry"))

    def emit(self, ext_fns: dict[ty.TyFun, set[id.Id]],
             ext_vars: dict[ty.TyArray | ty.TyTuple, set[id.Id]],
             ml_local_fns: list[cl.Function],
             mains: list[cl.Exp | cl.Cls | cl.LetBinding]) -> None:

        self._env.clear()
        self._mk_local_fn_env.clear()
        assert len(self.ir_main.blocks) == 1 and self.ir_main.blocks[0].name == 'entry'

        for ext_var_ty, ext_vars in ext_vars.items():
            self._env.update(self.get_ext_var_decl(ext_vars, ext_var_ty))

        for ext_fn_ty, ext_fns1 in ext_fns.items():
            self._env.update(self.get_fn_decl(ext_fns1, ext_fn_ty))

        self._env = self._env.new_child()

        # generate global function declarations
        for ml_fn in ml_local_fns:
            assert ml_fn.funct not in self._env, f"why function {ml_fn.funct} is already defined?"
            f, g = self.get_local_fn_decl(ml_fn)
            self._env[ml_fn.funct] = f
            self._mk_local_fn_env[ml_fn.funct] = g
        # initialization for global functions
        assert len(ml_local_fns) == len(self._env.maps[0])
        assert len(self._env.maps) == 2

        for ml_fn, ir_fn in zip(ml_local_fns, self._env.maps[0].values()):
            assert isinstance(ir_fn, ir.Function)
            assert len(self._env.maps[0]) == len(ml_local_fns)

            self.builder = ir.IRBuilder(ir_fn.blocks[0])

            with self._new_child_env(self._mk_local_fn_env[ml_fn.funct](self.builder)):
                del self._mk_local_fn_env[ml_fn.funct]
                r = self.visit(ml_fn.body)
                assert (r is None) == isinstance(IREmitter.get_ir_ty(ml_fn.typ.ret), ir.VoidType)
                if r is not None:
                    if r.name.startswith('.') or r.name == '':
                        r.name = '.ret'
                    self.builder.ret(r)
                else:
                    self.builder.ret_void()

        self.builder = ir.IRBuilder(self.ir_main.blocks[0])
        assert len(self._env.maps) == 2
        assert len(self._env.maps[0]) == len(ml_local_fns)
        for main in mains:
            if isinstance(main, cl.Exp):
                if (r := self.visit(main)) is not None:
                    r.name = ".ret.unused"
            elif isinstance(main, cl.Cls):
                raise NotImplementedError()
            else:
                rhs_val = self.visit(main.rhs)
                rhs_val.name = f"tmp.{main.lhs.idx}" if isinstance(main.lhs, id.TmpId) else str(main.lhs)
                self._env[main.lhs] = rhs_val

        self.builder.ret(ir.IntType(32)(0))

    def lookup(self, key: id.Id):
        v = self._env[key]
        if isinstance(v, ir.GlobalVariable):
            return self.builder.load(v)
        return v

    @contextlib.contextmanager
    def _new_child_env(self, env: dict[id.Id, tuple[ir.Function, ir.AllocaInstr] | ir.NamedValue | None]):
        self._env = self._env.new_child(env)
        try:
            yield
        finally:
            self._env = self._env.parents

    def visit(self, node: cl.Exp):
        v = super().visit(node)
        assert (v is None) == isinstance(IREmitter.get_ir_ty(node.typ), ir.VoidType)
        return v

    def visit_Lit(self, node: cl.Lit):
        match node.lit.val:
            case bool() as v:
                return IREmitter.get_ir_ty(node.typ)(v)
            case int() as v:
                return IREmitter.get_ir_ty(node.typ)(v)
            case float() as v:
                return IREmitter.get_ir_ty(node.typ)(v)
            case '()':
                return None
            case _:
                raise NotImplementedError()

    def visit_Var(self, node: cl.Var):
        return self.lookup(node.name)

    # def visit_Ext(self, node: cl.Ext):
    #     v = self._env.maps[-1][node.name]
    #     assert isinstance(v, ir.GlobalVariable)
    #     return self.builder.load(v)

    def visit_Get(self, node: cl.Get):
        arr = self.lookup(node.array)
        idx = self.lookup(node.index)
        gep = self.builder.gep(arr, [idx])
        r = self.builder.load(gep)
        if not isinstance(r.type, ir.VoidType):
            return r
        return None

    def visit_Unary(self, node: cl.Unary):
        match node.op.val:
            case kn.UnaryOpKind.I_NEG:
                return self.builder.neg(self.lookup(node.y))
            case kn.UnaryOpKind.F_NEG:
                return self.builder.fneg(self.lookup(node.y))
            case _:
                raise NotImplementedError()

    def visit_AppCls(self, node: cl.AppCls):
        callee = self.lookup(node.callee)
        args = [arg for arg in map(self.lookup, node.args) if arg is not None]
        if self.builder.function is callee:
            assert self.builder.function.args[-1].name == 'fv.struct.ptr'
            v = self.builder.call(callee, args + [self.builder.function.args[-1]], tail='tail')
            if not isinstance(v.type, ir.VoidType):
                return v
        else:
            entry_ptr = self.builder.extract_value(callee, 0, name=f"{callee.name}.entry.ptr")
            fv_ptr = self.builder.extract_value(callee, 1, name=f"{callee.name}.fv.ptr")
            cond = self.builder.icmp_signed('==', fv_ptr, ir.IntType(8).as_pointer()(None),
                                            name=f"{callee.name}.fv.ptr.null?")

            assert isinstance(entry_ptr.type, ir.PointerType) and isinstance(entry_ptr.type.pointee, ir.FunctionType)
            ftype = entry_ptr.type.pointee
            with self.builder.if_else(cond) as (then, otherwise):
                with then:
                    # remove the last argument
                    entry_ptr1 = self.builder.bitcast(
                        entry_ptr, ir.FunctionType(ftype.return_type, ftype.args[:-1]).as_pointer(),
                        name=f"{callee.name}.entry.ptr.direct")
                    v1 = self.builder.call(entry_ptr1, args, tail='tail')
                    v1.name = f"{callee.name}.direct.ret"
                    v1_block = self.builder.block
                    v1_block.name = f"{callee.name}.is.not.closure"
                with otherwise:
                    v2 = self.builder.call(entry_ptr, args + [fv_ptr], tail='tail')
                    v2.name = f"{callee.name}.closure.ret"
                    v2_block = self.builder.block
                    v2_block.name = f"{callee.name}.is.closure"
            if not isinstance(ftype.return_type, ir.VoidType):
                v = self.builder.phi(ftype.return_type, name=f"{callee.name}.ret")
                v.add_incoming(v1, v1_block)
                v.add_incoming(v2, v2_block)
                return v
        return None

    def visit_AppDir(self, node: cl.AppDir):
        callee = self.lookup(node.callee)
        assert isinstance(callee, ir.Function)
        args = [arg for arg in map(self.lookup, node.args) if arg is not None]
        if callee.function_type.return_type == ir.FloatType():
            return self.builder.call(callee, args, tail='tail', fastmath=('fast',))
        else:
            v = self.builder.call(callee, args, tail='tail')
            if not isinstance(v.type, ir.VoidType):
                return v
            return None

    def visit_Binary(self, node: cl.Binary):
        y1, y2 = self.lookup(node.y1), self.lookup(node.y2)
        assert y1 is not None and y2 is not None
        match node.op.val:
            case kn.BinaryOpKind.I_ADD:
                return self.builder.add(y1, y2)
            case kn.BinaryOpKind.F_ADD:
                return self.builder.fadd(y1, y2)
            case kn.BinaryOpKind.I_SUB:
                return self.builder.sub(y1, y2)
            case kn.BinaryOpKind.F_SUB:
                return self.builder.fsub(y1, y2)
            case kn.BinaryOpKind.I_MUL:
                return self.builder.mul(y1, y2)
            case kn.BinaryOpKind.I_DIV:
                return self.builder.sdiv(y1, y2)
            case kn.BinaryOpKind.F_MUL:
                return self.builder.fmul(y1, y2)
            case kn.BinaryOpKind.F_DIV:
                return self.builder.fdiv(y1, y2)
            case kn.BinaryOpKind.I_LT | kn.BinaryOpKind.I_GT | kn.BinaryOpKind.I_LE | kn.BinaryOpKind.I_GE as op:
                return self.builder.icmp_signed(str(op), y1, y2)
            case kn.BinaryOpKind.F_LT | kn.BinaryOpKind.F_GT | kn.BinaryOpKind.F_LE | kn.BinaryOpKind.F_GE as op:
                return self.builder.fcmp_ordered(str(op), y1, y2, flags=('fast',))
            case kn.BinaryOpKind.F_NEQ:
                return self.builder.fcmp_ordered('!=', y1, y2, flags=('fast',))
            case kn.BinaryOpKind.F_EQ:
                return self.builder.fcmp_ordered('==', y1, y2, flags=('fast',))
            case kn.BinaryOpKind.I_NEQ | kn.BinaryOpKind.B_NEQ:
                return self.builder.icmp_signed('!=', y1, y2)
            case kn.BinaryOpKind.I_EQ | kn.BinaryOpKind.B_EQ:
                return self.builder.icmp_signed('==', y1, y2)
            case _:
                raise NotImplementedError(node.op, node.typ)

    def visit_Seq(self, node: cl.Seq):
        r = None
        for e in node.es:
            r = self.visit(e)
        return r

    def visit_Tuple(self, node: cl.Tuple):
        tup_ty = IREmitter.get_ir_ty(node.typ)
        if isinstance(tup_ty, ir.VoidType):
            return None
        vs = [v for v in map(self.lookup, node.ys) if v is not None]
        if all(isinstance(v, ir.Constant) for v in vs):
            return tup_ty(vs)
        if isinstance(tup_ty, ir.LiteralStructType):
            assert len(vs) >= 2
            name = str(node.name) if node.name is not None else f'tuple.{len(vs)}'
            tup_ptr = self.builder.alloca(tup_ty, name=f"{name}.ptr")
            tup = self.builder.load(tup_ptr, name=f'{name}.initial')
            for i, v in enumerate(vs):
                tup = self.builder.insert_value(tup, v, i, name=f"{name}.elem.{i}.inserted")
                # gep = self.builder.gep(tup_ptr, [ir.IntType(32)(0), ir.IntType(32)(i)], name=f"elem-{i}.ptr")
                # self.builder.store(v, gep)
            tup.name = name
            return tup
        else:
            assert len(vs) == 1
            return vs[0]

    def visit_Put(self, node: cl.Put) -> None:
        arr = self.lookup(node.array)
        idx = self.lookup(node.index)
        val = self.lookup(node.value)
        gep = self.builder.gep(arr, [idx])
        self.builder.store(val or ir.IntType(8)(0), gep)


    def visit_If(self, node: cl.If) -> ir.PhiInstr | None:
        cond = self.lookup(node.cond)
        with self.builder.if_else(cond) as (then, otherwise):
            with then:
                br_true = self.visit(node.br_true)
                blk_true = self.builder.block
            with otherwise:
                br_false = self.visit(node.br_false)
                blk_false = self.builder.block
        t = IREmitter.get_ir_ty(node.typ)
        if not isinstance(t, ir.VoidType):
            assert br_true is not None and br_false is not None
            phi = self.builder.phi(t)
            phi.add_incoming(br_true, blk_true)
            phi.add_incoming(br_false, blk_false)
            return phi
        else:
            return None

    def visit_Let(self, node: cl.Let):
        rhs_val = self.visit(node.binding.rhs)
        with self._new_child_env({node.binding.lhs: rhs_val}):
            if isinstance(node.binding.lhs, id.TmpId):
                lhs_name = f"tmp.{node.binding.lhs.idx}"
            else:
                lhs_name = str(node.binding.lhs)
            if rhs_val is not None:
                rhs_val.name = lhs_name
            return self.visit(node.expr)

    def visit_LetTuple(self, node: cl.LetTuple):
        y = self.lookup(node.y)
        if y is None:
            self._env = self._env.new_child({x: None for x in node.xs})
        else:
            # assert isinstance(y.type, ir.LiteralStructType)
            # assert len(y.type.elements) == len(node.xs)
            self._env = self._env.new_child()
            non_void_xs, non_void_ts, void_xs = partition(zip(node.xs, node.ts))
            for void_x in void_xs:
                self._env[void_x] = None
            if len(non_void_xs) == 1:
                self._env[non_void_xs[0]] = y
            else:
                for i, non_void_x in enumerate(non_void_xs):
                    self._env[non_void_x] = self.builder.extract_value(y, i, name=str(non_void_x))
        res = self.visit(node.e)
        self._env = self._env.parents
        return res

    def visit_MakeCls(self, node: cl.MakeCls):
        cls_entry_func = self.lookup(node.closure.entry.funct)
        i8_ptr_ty = ir.IntType(8).as_pointer()
        assert isinstance(cls_entry_func, ir.Function)
        arg_fv_struct_ptr = cls_entry_func.args[-1]
        if arg_fv_struct_ptr.name == 'fv.struct.ptr':
            # make object to pass free variables
            actual_fv_prefix = f"{cls_entry_func.name}.actual.fv.struct"
            actual_fv_struct_ptr = self.builder.alloca(arg_fv_struct_ptr.type.pointee, name=f"{actual_fv_prefix}.ptr")
            actual_fv_struct = self.builder.load(actual_fv_struct_ptr, name=f"{actual_fv_prefix}.uninitialized")
            actual_fv = [fv for fv in map(self.lookup, node.closure.actual_fv) if fv is not None]
            for i, fv in enumerate(actual_fv):
                actual_fv_struct = self.builder.insert_value(
                    actual_fv_struct, fv, i, name=f"{actual_fv_prefix}.{i}.inserted")
            actual_fv_struct.name = actual_fv_prefix
            self.builder.store(actual_fv_struct, actual_fv_struct_ptr)

            # cast all types of fv object pointers to i8*, and so does the fv argument of the closure entry function
            cls_entry_ty_downcast = ir.FunctionType(cls_entry_func.ftype.return_type,
                                                    [*cls_entry_func.ftype.args[:-1], i8_ptr_ty])
            cls_entry_downcast = self.builder.bitcast(cls_entry_func, cls_entry_ty_downcast.as_pointer())
            cls_entry_downcast.name = f"{cls_entry_func.name}.as_ptr.downcast"
            actual_fv_struct_ptr_downcast = self.builder.bitcast(actual_fv_struct_ptr, i8_ptr_ty)
            actual_fv_struct_ptr_downcast.name = f"{actual_fv_struct_ptr.name}.downcast"
            cls_ptr = self.builder.alloca(ir.LiteralStructType([cls_entry_downcast.type, i8_ptr_ty]))
            cls_ptr.name = f"{cls_entry_func.name}.closure.ptr"

            cls_entry_ptr = self.builder.gep(cls_ptr, [ir.IntType(32)(0), ir.IntType(32)(0)])
            cls_entry_ptr.name = f"{cls_entry_func.name}.closure.entry.ptr"
            self.builder.store(cls_entry_downcast, cls_entry_ptr)

            cls_fv_ptr = self.builder.gep(cls_ptr, [ir.IntType(32)(0), ir.IntType(32)(1)])
            cls_fv_ptr.name = f"{cls_entry_func.name}.closure.fv.ptr"
            self.builder.store(actual_fv_struct_ptr_downcast, cls_fv_ptr)
            cls = self.builder.load(cls_ptr, name=f"{cls_entry_func.name}.closure")
        else:
            cls_entry_ty_lift = ir.FunctionType(cls_entry_func.ftype.return_type,
                                                [*cls_entry_func.ftype.args, i8_ptr_ty])
            cls_entry_lift = self.builder.bitcast(cls_entry_func, cls_entry_ty_lift.as_pointer())
            cls_entry_lift.name = f"{cls_entry_func.name}.as_ptr.lift"
            cls_ptr = self.builder.alloca(ir.LiteralStructType([cls_entry_lift.type, i8_ptr_ty]))
            cls_ptr.name = f"{cls_entry_func.name}.closure.ptr"
            cls_entry_ptr = self.builder.gep(cls_ptr, [ir.IntType(32)(0), ir.IntType(32)(0)])
            cls_entry_ptr.name = f"{cls_entry_func.name}.closure.entry.ptr"
            self.builder.store(cls_entry_lift, cls_entry_ptr)
            cls_fv_ptr = self.builder.gep(cls_ptr, [ir.IntType(32)(0), ir.IntType(32)(1)])
            cls_fv_ptr.name = f"{cls_entry_func.name}.closure.fv.ptr"
            self.builder.store(i8_ptr_ty(None), cls_fv_ptr)
            cls = self.builder.load(cls_ptr, name=f"{cls_entry_func.name}.closure")

        with self._new_child_env({node.closure.entry.funct: cls}):
            return self.visit(node.body)


if __name__ == '__main__':
    dbl = ir.DoubleType()
    void = ir.IntType(1)
    fnty = ir.FunctionType(dbl, (void, void))

    module = ir.Module(name=__file__)
    func = ir.Function(module, fnty, name="foo")

    block = func.append_basic_block(name="entry")
    builder = ir.IRBuilder(block)
    a, b = func.args
    c = builder.add(a, b, name="c")
    d = builder.add(ir.Constant(ir.IntType(32), 1), ir.Constant(ir.IntType(32), 2))
    builder.ret(c)
    print(module)
