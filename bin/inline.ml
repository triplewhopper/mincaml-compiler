open KNormal

(** インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 0 (* Mainで-inlineオプションによりセットされる *)

let rec size kn = match kn.value with
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1;_}, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let rec g env kn = 
  let return value = if equal_exp value kn.value then kn else { kn with value; prev = PrevLeft kn } in
  match kn.value with (** インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2) |> return
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2) |> return
  | Let(xt, e1, e2) -> Let(xt, g env e1, g env e2) |> return
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
      let env = if size e1 > !threshold then env else M.add x (yts, e1) env in
      LetRec({ name = (x, t); args = yts; body = g env e1}, g env e2) |> return
  | App(x, ys) when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
      let (zs, e) = M.find x env in (* zs: 仮引数のリスト, e: 関数本体 *)
      Format.eprintf "inlining %a@." Id.pp x;
      let env' = (* 仮引数と実引数の置換 *)
        List.fold_left2
          (fun env' (z, _t) y -> M.add z y env')
          M.empty
          zs
          ys in
      let expanded = Alpha.g env' e in { expanded with prev = PrevLeft kn}
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e) |> return
  | e -> e |> return

let f e = g M.empty e
