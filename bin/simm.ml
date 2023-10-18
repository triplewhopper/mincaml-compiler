open Asm

let rec g env asm = 
  let return value = { asm with value; prev = KNormal.PrevLeft asm} in
  match asm.value with (** 命令列の即値最適化 (caml2html: simm13_g) *)
  | Ans(exp) -> Ans(g' env exp) |> return
  | Let((x, t), Set(i), tk, e) -> (* 即値のセットの除去 (caml2html: simm13_let) *)
      (* Format.eprintf "found simm %s = %d@." x i; *)
      let e' = g (M.add x i env) e in
      if List.mem x (fv e') then return (Let((x, t), Set(i), tk, e')) else
      ((* Format.eprintf "erased redundant Set to %s@." x; *)
       e')
  | Let(xt, exp, tk, e) -> Let(xt, g' env exp, tk, g env e) |> return
and g' env = function (** 各命令の即値最適化 (caml2html: simm13_gprime) *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env)) 
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env)) 
  | Sub(x, V(y)) when M.mem y env -> Sub(x, C(M.find y env)) 
  | Ld(x, V(y), i) when M.mem y env -> Ld(x, C(M.find y env), i)
  | St(x, y, V(z), i) when M.mem z env -> St(x, y, C(M.find z env), i)
  | LdDF(x, V(y), i) when M.mem y env -> LdDF(x, C(M.find y env), i)
  | StDF(x, y, V(z), i) when M.mem z env -> StDF(x, y, C(M.find z env), i)
  | IfEq(x, V(y), e1, e2) when M.mem y env -> IfEq(x, C(M.find y env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem y env -> IfLE(x, C(M.find y env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem y env -> IfGE(x, C(M.find y env), g env e1, g env e2)
  | IfEq(x, V(y), e1, e2) when M.mem x env -> IfEq(y, C(M.find x env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem x env -> IfGE(y, C(M.find x env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem x env -> IfLE(y, C(M.find x env), g env e1, g env e2)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfGE(x, y', e1, e2) -> IfGE(x, y', g env e1, g env e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

let h { name = l; args = xs; fargs = ys; body = e; ret = t; link = kn} = (** トップレベル関数の即値最適化 *)
  { name = l; args = xs; fargs = ys; body = g M.empty e; ret = t; link = kn}

let f (Prog(data, fundefs, e)) = (** プログラム全体の即値最適化 *)
  Prog(data, List.map h fundefs, g M.empty e)
