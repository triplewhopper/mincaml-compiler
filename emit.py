import logging
from typing import List, Set, Dict, Tuple as Tup
import llvmlite.ir as ir
import llvmlite.binding as binding
import closure as cl
import knormal as kn
from withbounds import WithBounds
from collections import ChainMap
from functools import lru_cache
import ty

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

x64_layout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
x64_triple = "x86_64-apple-macosx13.0.0"
rv32_layout = "e-m:e-p:32:32-i64:64-n32-S128"
rv32_triple = "riscv32"
target_data = binding.create_target_data(rv32_layout)


#
# class ExtCollector(cl.ExpVisitor[None]):
#     def __init__(self, ml_global_fns: List[cl.Function]):
#         self._exts: Dict[kn.GlobalId, ir.GlobalVariable | ir.Function] = {}
#         self._env: ChainMap[kn.Id, ty.Ty] = ChainMap({fn.funct: fn.get_type() for fn in ml_global_fns})
#         for fn in ml_global_fns:
#             self._env.update(dict(fn.iter_args()))
#             self.visit(fn.body)
#             self._env = self._env.parents
#
#     @property
#     def exts(self) -> Dict[kn.GlobalId, ir.GlobalVariable | ir.Function]:
#         return self._exts
#
#     def on_id(self, x: kn.Id) -> None:
#         assert isinstance(x, kn.Id)
#         ml_ext_ty = self._env[x]
#         if isinstance(x, kn.GlobalId):
#             if isinstance(ml_ext_ty, ty.TyFun):
#
#             elif isinstance(ml_ext_ty, ty.TyArray):
#                 ir_ext_arr_ty = IREmitter.get_ir_ty(ml_ext_ty)
#                 ir_ext_arr = ir.GlobalVariable(module=None, typ=ir_ext_arr_ty, name=x.val.val)
#                 ir_ext_arr.unnamed_addr = True
#                 logger.info(f"Creating external array '{x.val.val}'")
#                 self._exts[x] = ir_ext_arr
#             else:
#                 raise NotImplementedError()
#
#     def visit_Lit(self, node: cl.Lit) -> None:
#         ...
#
#     def visit_Var(self, node: cl.Var) -> None:
#         self.on_id(node.name)
#
#     visit_Ext = visit_Var
#
#     def visit_Get(self, node: cl.Get) -> None:
#         self.on_id(node.array)
#         self.on_id(node.index)
#
#     def visit_Unary(self, node: cl.Unary) -> None:
#         self.visit(node.e)
#
#     def visit_AppCls(self, node: cl.AppCls) -> None:
#         self.on_id(node.callee)
#         for arg in node.args:
#             self.on_id(arg)
#
#     visit_AppDir = visit_AppCls
#
#     def visit_Binary(self, node: cl.Binary) -> None:
#         self.on_id(node.e1)
#         self.on_id(node.e2)
#
#     def visit_Tuple(self, node: cl.Tuple) -> None:
#         for e in node.elems:
#             self.on_id(e)
#
#     def visit_Put(self, node: cl.Put) -> None:
#         self.on_id(node.array)
#         self.on_id(node.index)
#         self.on_id(node.value)
#
#     def visit_If(self, node: cl.If) -> None:
#         self.on_id(node.cond)
#         self.visit(node.br_true)
#         self.visit(node.br_false)
#
#     def visit_Let(self, node: cl.Let) -> None:
#         self.visit(node.rhs)
#         self._env = self._env.new_child({node.lhs: node.rhs.get_type()})
#         self.visit(node.expr)
#         self._env = self._env.parents
#
#     def visit_LetTuple(self, node: cl.LetTuple) -> None:
#         self.on_id(node.e1)
#         e1_ty = self._env[node.e1]
#         assert isinstance(e1_ty, ty.TyTuple)
#         assert len(e1_ty.elems) == len(node.xs)
#         self._env = self._env.new_child(dict(zip(node.xs, e1_ty.elems)))
#         self.visit(node.e2)
#         self._env = self._env.parents
#
#     def visit_MakeCls(self, node: cl.MakeCls) -> None:
#         c = node.closure
#         assert isinstance(c.entry, cl.Function)
#         self._env = self._env.new_child({c.entry.funct: c.entry.get_type()})
#         self.visit(node.body)
#         self._env.update(dict(c.entry.iter_args()))
#         self.visit(c.entry.body)
#         self._env = self._env.parents
#

class IREmitter(cl.ExpVisitor[ir.NamedValue | ir.Constant]):
    @staticmethod
    @lru_cache(maxsize=128)
    def get_ir_ty(typ: ty.Ty) -> ir.Type:
        match typ:
            case ty.TyUnit():
                # TODO:
                #  optimize unit to void, e.g. a function of type unit -> unit should be void -> void
                #  likewise, unit array should be void array, i.e. void*, and every read/write should be a no-op,
                #  as long as there is no side effect.
                return ir.IntType(8)
            case ty.TyInt():
                return ir.IntType(32)
            case ty.TyFloat():
                return ir.FloatType()
            case ty.TyBool():
                return ir.IntType(8)
            case ty.TyTuple(elems):
                ir_ty = ir.LiteralStructType([IREmitter.get_ir_ty(e) for e in elems])
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
                args_ir_ty = [IREmitter.get_ir_ty(a) for a in args]
                ir_ty = ir.FunctionType(IREmitter.get_ir_ty(ret), args_ir_ty)
                ir_ty = ir.PointerType(ir_ty)
                logger.info(f"min-caml type '{typ}' maps to LLVM type '{ir_ty}'")
                return ir_ty

    def get_fn_decl(self, fns: Set[kn.GlobalId], ml_ty: ty.TyFun) -> Dict[kn.GlobalId, ir.Function]:
        declared: Dict[str, ir.Function] = {}
        ans: Dict[kn.GlobalId, ir.Function] = {}
        ir_ext_fn_ty = ir.FunctionType(
            IREmitter.get_ir_ty(ml_ty.ret),
            [IREmitter.get_ir_ty(a) for a in ml_ty.args])
        assert isinstance(ir_ext_fn_ty, ir.FunctionType)
        for fn in fns:
            name = fn.val.val
            if name in ('Array.make', 'Array.create'):
                name = f"create_array_{str(ml_ty.args[1]).strip().replace(' ', '_')}"
            if name not in declared:
                ir_fn_decl = ir.Function(module=self.module, ftype=ir_ext_fn_ty, name='min_caml_' + name)
                logger.info(f"Creating external function declaration @{ir_fn_decl.name} of type '{ir_fn_decl.type}'")

                assert len(ml_ty.args) == len(ir_fn_decl.args)
                for i, arg in zip(range(len(ml_ty.args)), ir_fn_decl.args):
                    arg.add_attribute('noundef')
                    # arg.name = f"arg{i}"

                ir_fn_decl.global_constant = True
                # ir_decl.initializer = ir.Constant(ty, None)
                ir_fn_decl.unnamed_addr = True
                ans[fn] = ir_fn_decl
                declared[name] = ir_fn_decl
            else:
                ans[fn] = declared[name]
        return ans

    def get_arr_decl(self, arrs: Set[kn.GlobalId], ml_ext_ty: ty.TyArray) -> Dict[kn.GlobalId, ir.GlobalVariable]:
        declared: Dict[str, ir.GlobalVariable] = {}
        ans: Dict[kn.GlobalId, ir.GlobalVariable] = {}
        ir_ext_arr_ty = IREmitter.get_ir_ty(ml_ext_ty)
        for arr in arrs:
            if arr.val.val not in declared:
                ir_ext_arr_decl = ir.GlobalVariable(module=self.module, typ=ir_ext_arr_ty, name=arr.val.val)
                ir_ext_arr_decl.unnamed_addr = True
                ir_ext_arr_decl.global_constant = True
                logger.info(f"Creating external array @{ir_ext_arr_decl.name} of type '{ir_ext_arr_decl.type}'")
                ans[arr] = ir_ext_arr_decl
                declared[arr.val.val] = ir_ext_arr_decl
            else:
                ans[arr] = declared[arr.val.val]

        return ans

    def __init__(self, ext_fns: Dict[ty.TyFun, Set[kn.GlobalId]], ext_arrays: Dict[ty.TyArray, Set[kn.GlobalId]],
                 ml_global_fns: List[cl.Function], main: cl.Exp):
        # module
        self.module = ir.Module(name=__file__)
        self.module.triple = rv32_triple
        self.module.data_layout = rv32_layout

        # functions
        ir_main_ty = ir.FunctionType(ir.IntType(32), [])
        # self.ir_global_fns: Dict[WithBounds[str], ir.Function] = {}

        self.ir_main = ir.Function(self.module, ir_main_ty, name='caml_main')
        logger.info(f"Creating function @{self.ir_main.name} with type '{ir_main_ty}'")
        self.ir_main.append_basic_block(name="entry")

        self._env: ChainMap[kn.Id, ir.NamedValue] = ChainMap()
        del ir_main_ty

        for ext_arr_ty, ext_arrs in ext_arrays.items():
            self._env.update(self.get_arr_decl(ext_arrs, ext_arr_ty))

        for ext_fn_ty, ext_fns in ext_fns.items():
            self._env.update(self.get_fn_decl(ext_fns, ext_fn_ty))

        self._env = self._env.new_child()
        # generate global function declarations
        for ml_fn in ml_global_fns:
            arg_tys = map(IREmitter.get_ir_ty, (t for _, t in ml_fn.iter_args()))
            fv_tys = list(map(IREmitter.get_ir_ty, (t for _, t in ml_fn.formal_fv)))
            fn_ir_ret_ty = IREmitter.get_ir_ty(ml_fn.get_return_type())
            if fv_tys:
                fv_struct_ptr_ty = ir.PointerType(ir.LiteralStructType(fv_tys))
                ml_fn_ir_ty = ir.FunctionType(fn_ir_ret_ty, [*arg_tys, fv_struct_ptr_ty])
            else:
                fv_struct_ptr_ty = None
                ml_fn_ir_ty = ir.FunctionType(fn_ir_ret_ty, arg_tys)

            del arg_tys, fn_ir_ret_ty

            assert ml_fn.funct not in self._env, f"why function {ml_fn.funct} is already defined?"
            ir_fn = ir.Function(self.module, ml_fn_ir_ty, name=ml_fn.funct.val.val)
            # ir_fn.calling_convention = 'tailcc'
            ir_fn.append_basic_block(name="entry")
            logger.info(f"Creating local function declaration @{ir_fn.name} of type '{ir_fn.type}'")
            if fv_struct_ptr_ty is not None:
                logger.info(
                    f"function @{ir_fn.name} has an extra argument of type '{fv_struct_ptr_ty}' for passing free variables")

            self._env[ml_fn.funct] = ir_fn
            for i, arg in zip(range(ml_fn.get_n_args()), ir_fn.args):
                arg.add_attribute('noundef')
                arg.name = str(ml_fn.get_arg_name(i))

            if fv_tys:
                ir_fn.args[-1].name = "fv.struct.ptr"
                ir_fn.args[-1].add_attribute('nonnull')
                ir_fn.args[-1].add_attribute('noundef')
            del ml_fn_ir_ty

        # initialization for global functions
        assert len(ml_global_fns) == len(self._env.maps[0])
        assert len(self._env.maps) == 2

        for ml_fn, ir_fn in zip(ml_global_fns, self._env.maps[0].values()):
            assert isinstance(ir_fn, ir.Function)
            self.builder = ir.IRBuilder(ir_fn.blocks[0])
            assert len(self._env.maps[0]) == len(ml_global_fns)

            ir_fn_local_env = {}
            for i, arg in zip(range(ml_fn.get_n_args()), ir_fn.args):
                name_i = ml_fn.get_arg_name(i)
                ir_fn_local_env[name_i] = arg

            if ml_fn.get_n_args() != len(ir_fn.args):
                raise NotImplementedError("TODO: handle free variables")
                # assert ml_fn.get_n_args() + 1 == len(ir_fn.args)
                # fv_struct_ptr = ir_fn.args[-1]
                # assert isinstance(fv_struct_ptr.type, ir.PointerType)
                # assert isinstance(fv_struct_ptr.type.pointee, ir.LiteralStructType)
                # assert len(ml_fn.formal_fv) == len(fv_struct_ptr.type.pointee.elements)
                # for i, ((elem, _), elem_ty) in enumerate(zip(ml_fn.formal_fv, fv_struct_ptr.type.pointee.elements)):
                #     fv_elem_ptr = self.builder.gep(fv_struct_ptr, [ir.IntType(32)(0), ir.IntType(32)(i)])
                #     ir_fn_local_env[elem] = self.builder.load(fv_elem_ptr, name=f"fv.{elem.val}")

            self._env = self._env.new_child(ir_fn_local_env)
            del ir_fn_local_env, i, arg

            self.builder.ret(self.visit(ml_fn.body))
            self._env: ChainMap[kn.Id, ir.NamedValue] = self._env.parents

        self.builder = ir.IRBuilder(self.ir_main.blocks[0])
        assert len(self._env.maps) == 2
        assert len(self._env.maps[0]) == len(ml_global_fns)
        self.visit(main)
        self.builder.ret(ir.IntType(32)(0))

    def lookup(self, key: kn.Id) -> ir.NamedValue | ir.Constant | ir.LoadInstr:
        v = self._env[key]
        if isinstance(v, ir.GlobalVariable):
            return self.builder.load(v)
        return v

    def visit(self, node: cl.Exp) -> ir.NamedValue | ir.Constant:
        v = super().visit(node)
        assert v.type == IREmitter.get_ir_ty(
            node.get_type()) or v.type == ir.VoidType() and node.get_type() is ty.TyUnit()
        return v

    def visit_Lit(self, node: cl.Lit) -> ir.Constant:
        match node.val.val:
            case bool() as v:
                return IREmitter.get_ir_ty(node.get_type())(int(v))
            case int() as v:
                return IREmitter.get_ir_ty(node.get_type())(v)
            case float() as v:
                return IREmitter.get_ir_ty(node.get_type())(v)
            case '()':
                return ir.IntType(8)(0)
            case _:
                raise NotImplementedError()

    def visit_Var(self, node: cl.Var) -> ir.NamedValue | ir.Constant | ir.LoadInstr:
        return self.lookup(node.name)

    def visit_Ext(self, node: cl.Ext) -> ir.LoadInstr:
        v = self._env.maps[-1][node.name]
        assert isinstance(v, ir.GlobalVariable)
        return self.builder.load(v)

    # def visit_ExtArray(self, node: cl.ExtArray) -> ir.GlobalVariable:
    # generate external function declarations
    # try:
    #     res = self.env[node.name]
    #     assert isinstance(res, ir.GlobalVariable)
    #     assert isinstance(res.type, ir.PointerType)
    #     return res
    # except:
    #     assert node.name not in self.env, f"array {node.name} is already defined"
    #     logging.info(f"Creating external array '{node.name.val.val}'")
    #     ir_ext_arr_ty = IREmitter.get_ir_ty(node.get_type())
    #     ir_ext_arr = ir.GlobalVariable(self.module, ir_ext_arr_ty, name=node.name.val.val)
    #     ir_ext_arr.unnamed_addr = True
    #     self.env.maps[-1][node.name] = ir_ext_arr
    #     return ir_ext_arr

    # def visit_ExtFun(self, node: cl.ExtFun) -> ir.Function:
    # try:
    #     res = self.env[node.name]
    #     assert isinstance(res, ir.Function)
    #     return res
    # except KeyError:
    #     ml_ext_ty = node.get_type()
    #     ir_ext_fn_ty = ir.FunctionType(
    #         IREmitter.get_ir_ty(ml_ext_ty.ret),
    #         [IREmitter.get_ir_ty(a) for a in ml_ext_ty.args])
    #     assert isinstance(ir_ext_fn_ty, ir.FunctionType)
    #     assert node.name not in self.env, f"function {node.name} is already defined"
    #     ir_ext_fn = ir.Function(self.module, ir_ext_fn_ty, name=node.name.val.val)
    #     logger.info(f"Creating function @{ir_ext_fn.name} with type '{ir_ext_fn.type}'")
    #     self.env.maps[-1][node.name] = ir_ext_fn
    #     assert len(ml_ext_ty.args) == len(ir_ext_fn.args)
    #     for i, arg in zip(range(len(ml_ext_ty.args)), ir_ext_fn.args):
    #         arg.add_attribute('noundef')
    #         arg.name = f"arg{i}"
    #     del ir_ext_fn_ty
    #     return ir_ext_fn

    def visit_Get(self, node: cl.Get) -> ir.LoadInstr:
        arr = self.lookup(node.array)
        idx = self.lookup(node.index)
        gep = self.builder.gep(arr, [idx])
        return self.builder.load(gep)

    def visit_Unary(self, node: cl.Unary) -> ir.Instruction:
        match node.op:
            case kn.Unary.OpKind.I_NEG:
                return self.builder.neg(self.lookup(node.e))
            case kn.Unary.OpKind.F_NEG:
                return self.builder.fneg(self.lookup(node.e))
            case _:
                raise NotImplementedError()

    def visit_AppCls(self, node: cl.AppCls) -> ir.CallInstr:
        raise NotImplementedError()
        callee = self, lookup(node.callee)
        return self.builder.call(
            callee, [self.lookup(e) for e in node.args], tail='tail')

    def visit_AppDir(self, node: cl.AppDir) -> ir.CallInstr:
        callee = self.lookup(node.callee)
        assert isinstance(callee, ir.Function)
        if callee.function_type.return_type == ir.FloatType():
            fastmath = ('fast',)
        else:
            fastmath = ()
        return self.builder.call(
            callee, [self.lookup(e) for e in node.args], tail='tail',
            fastmath=fastmath)

    def visit_Binary(self, node: cl.Binary) -> ir.Instruction | ir.NamedValue | ir.Constant:
        e1, e2 = self.lookup(node.e1), self.lookup(node.e2)
        match node.op:
            case kn.Binary.OpKind.I_ADD:
                return self.builder.add(e1, e2)
            case kn.Binary.OpKind.F_ADD:
                return self.builder.fadd(e1, e2)
            case kn.Binary.OpKind.I_SUB:
                return self.builder.sub(e1, e2)
            case kn.Binary.OpKind.F_SUB:
                return self.builder.fsub(e1, e2)
            case kn.Binary.OpKind.F_MUL:
                return self.builder.fmul(e1, e2)
            case kn.Binary.OpKind.F_DIV:
                return self.builder.fdiv(e1, e2)
            case kn.Binary.OpKind.I_LT | kn.Binary.OpKind.I_GT | kn.Binary.OpKind.I_LE | kn.Binary.OpKind.I_GE as op:
                r = self.builder.icmp_signed(str(op), e1, e2)
                return self.builder.zext(r, ir.IntType(8))
            case kn.Binary.OpKind.F_LT | kn.Binary.OpKind.F_GT | kn.Binary.OpKind.F_LE | kn.Binary.OpKind.F_GE as op:
                r = self.builder.fcmp_ordered(str(op), e1, e2, flags=('fast',))
                return self.builder.zext(r, ir.IntType(8))
            case kn.Binary.OpKind.F_NEQ:
                r = self.builder.fcmp_ordered('!=', e1, e2, flags=('fast',))
                return self.builder.zext(r, ir.IntType(8))
            case kn.Binary.OpKind.F_EQ:
                r = self.builder.fcmp_ordered('==', e1, e2, flags=('fast',))
                return self.builder.zext(r, ir.IntType(8))
            case kn.Binary.OpKind.I_NEQ | kn.Binary.OpKind.B_NEQ:
                r = self.builder.icmp_signed('!=', e1, e2)
                return self.builder.zext(r, ir.IntType(8))
            case kn.Binary.OpKind.I_EQ | kn.Binary.OpKind.B_EQ:
                r = self.builder.icmp_signed('==', e1, e2)
                return self.builder.zext(r, ir.IntType(8))
            # case kn.Binary.OpKind.SEQ:
            #     return e2
            case _:
                raise NotImplementedError(node.op, node.get_type())

    def visit_Seq(self, node: cl.Seq) -> ir.NamedValue | ir.Constant:
        r = None
        for e in node.es:
            r = self.visit(e)
        assert r is not None
        return r

    def visit_Tuple(self, node: cl.Tuple) -> ir.Constant | ir.NamedValue:
        tup_ty = IREmitter.get_ir_ty(node.get_type())
        assert isinstance(tup_ty, ir.LiteralStructType)
        vs = [self.lookup(e) for e in node.elems]
        if all(isinstance(v, ir.Constant) for v in vs):
            return tup_ty(vs)
        tup_ptr = self.builder.alloca(tup_ty, name="tuple.ptr")
        for i, v in enumerate(vs):
            gep = self.builder.gep(tup_ptr, [ir.IntType(32)(0), ir.IntType(32)(i)], name=f"elem-{i}.ptr")
            self.builder.store(v, gep)
        return self.builder.load(tup_ptr, name="tuple")

    def visit_Put(self, node: cl.Put) -> ir.Constant:
        arr = self.lookup(node.array)
        idx = self.lookup(node.index)
        val = self.lookup(node.value)
        gep = self.builder.gep(arr, [idx])
        self.builder.store(val, gep)
        return ir.IntType(8)(0)

    def visit_If(self, node: cl.If) -> ir.PhiInstr:
        cond = self.lookup(node.cond)
        cond = self.builder.trunc(cond, ir.IntType(1))
        with self.builder.if_else(cond) as (then, otherwise):
            with then:
                assert isinstance(node.br_true, cl.Exp)
                br_true = self.visit(node.br_true)
                blk_true = self.builder.block
                # blk_true.name = blk_true.name + '@' + str(node.br_true.bounds[0]) + ':' + str(node.br_true.bounds[1])
            with otherwise:
                assert isinstance(node.br_false, cl.Exp)
                br_false = self.visit(node.br_false)
                blk_false = self.builder.block
                # blk_false.name = blk_false.name + '@' + str(node.br_false.bounds[0]) + ':' + str(
                #     node.br_false.bounds[1])
                # ...
        phi = self.builder.phi(IREmitter.get_ir_ty(node.get_type()))
        phi.add_incoming(br_true, blk_true)
        phi.add_incoming(br_false, blk_false)
        return phi

    # def store_tuple(self, val: ir.NamedValue | ir.Constant, dst_ptr: ir.NamedValue, idx=()):
    #     assert isinstance(val.type, ir.LiteralStructType)
    #     assert isinstance(dst_ptr.type, ir.PointerType)
    #     assert dst_ptr.type.pointee == val.type
    #     for i, e in enumerate(val.type.elements):
    #         elem_ptr = self.builder.gep(dst_ptr, [ir.IntType(32)(0), ir.IntType(32)(i)],
    #                                     name=f"elem-<{'>-<'.join(idx + (str(i),))}>.ptr")
    #         v = self.builder.extract_value(val, i, name=f"elem-<{'>-<'.join(idx + (str(i),))}>")
    #         if isinstance(v.type, ir.LiteralStructType):
    #             self.store_tuple(v, elem_ptr, idx=idx + (str(i),))
    #         else:
    #             self.builder.store(v, elem_ptr)

    def visit_Let(self, node: cl.Let) -> ir.NamedValue | ir.Constant:
        rhs_val = self.visit(node.rhs)
        lhs_name = str(node.lhs)
        lhs_ptr = self.builder.alloca(IREmitter.get_ir_ty(node.rhs.get_type()))
        # if node.rhs.get_type() is ty.TyUnit():
        #     self.builder.store(ir.IntType(8)(0), lhs_ptr)
        # else:
        self.builder.store(rhs_val, lhs_ptr)
        self._env = self._env.new_child({node.lhs: self.builder.load(lhs_ptr, name=lhs_name)})
        res = self.visit(node.expr)
        self._env = self._env.parents
        return res

    def visit_LetTuple(self, node: cl.LetTuple) -> ir.NamedValue | ir.Constant:
        y = self.lookup(node.e1)
        assert isinstance(y.type, ir.LiteralStructType)
        assert len(y.type.elements) == len(node.xs)
        self._env = self._env.new_child()
        xs_ptr = self.builder.alloca(y.type, name="tuple.ptr")
        self.builder.store(y, xs_ptr)
        for i, x in enumerate(node.xs):
            gep = self.builder.gep(xs_ptr, [ir.IntType(32)(0), ir.IntType(32)(i)], name=f"{str(x)}.ptr")
            self._env[x] = self.builder.load(gep, name=str(x))
        res = self.visit(node.e2)
        self._env = self._env.parents
        return res

    def visit_MakeCls(self, node: cl.MakeCls) -> ir.Value:
        raise NotImplementedError()
        cls_ir_ty = self.module.context.get_identified_type(node.closure.entry.funct.val)
        # cls_ir_ty.


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
