(** flatten {i let}-bindings (just for prettier printing) *)

open KNormal

let rec f = fun kn -> 
  let return kn value = if equal_exp value kn.value then kn else { kn with value; prev=PrevLeft kn} in
  match kn.value with (** ネストしたletの簡約 (caml2html: assoc_f) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, f e1, f e2) |> return kn
  | IfLE(x, y, e1, e2) -> IfLE(x, y, f e1, f e2) |> return kn
  | Let(xt, e1, e2) -> (* letの場合 (caml2html: assoc_let) *)
      let rec insert kn1 = match kn1.value with
        | Let(yt, e3, e4) -> Let(yt, e3, insert e4) |> return kn1
        | LetRec(fundefs, e) -> LetRec(fundefs, insert e) |> return kn1
        | LetTuple(yts, z, e) -> LetTuple(yts, z, insert e) |> return kn1
        | e -> Let(xt, kn1, f e2) |> return kn in
      insert (f e1)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = f e1 }, f e2) |> return kn
  | LetTuple(xts, y, e) -> LetTuple(xts, y, f e) |> return kn
  | e -> e |> return kn
