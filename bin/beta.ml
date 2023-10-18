(* open KNormal *)

let find x env = try M.find x env with Not_found -> x (** 置換のための関数 (caml2html: beta_find) *)

let rec g env kn = 
  let open KNormal in
  let return value = if equal_exp value kn.value then kn else {kn with value; prev = PrevLeft kn} in
  match kn.value with (** β簡約ルーチン本体 (caml2html: beta_g) *)
  | Unit -> Unit |> return
  | Int(i) -> Int(i) |> return
  | Float(d) -> Float(d) |> return
  | Neg(x) -> Neg(find x env) |> return
  | Add(x, y) -> Add(find x env, find y env) |> return
  | Sub(x, y) -> Sub(find x env, find y env) |> return
  | FNeg(x) -> FNeg(find x env) |> return
  | FAdd(x, y) -> FAdd(find x env, find y env) |> return
  | FSub(x, y) -> FSub(find x env, find y env) |> return
  | FMul(x, y) -> FMul(find x env, find y env) |> return
  | FDiv(x, y) -> FDiv(find x env, find y env) |> return
  | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, g env e1, g env e2) |> return
  | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, g env e1, g env e2) |> return
  | Let((x, t), e1, e2) -> (* letのβ簡約 (caml2html: beta_let) *)
      (match g env e1 with
      | {value=Var(y);_} ->
          Format.eprintf "@[beta-reducing@ %a@ =@ %a@]@." Id.pp x Id.pp y;
          g (M.add x y env) e2
      | e1' ->
          let e2' = g env e2 in
          Let((x, t), e1', e2') |> return) 
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = g env e1 }, g env e2) |> return
  | Var(x) -> Var(find x env) |> return (* 変数を置換 (caml2html: beta_var) *)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs) |> return
  | LetTuple(xts, y, e) -> LetTuple(xts, find y env, g env e) |> return
  | Get(x, y) -> Get(find x env, find y env) |> return
  | Put(x, y, z) -> Put(find x env, find y env, find z env) |> return
  | App(g, xs) -> App(find g env, List.map (fun x -> find x env) xs) |> return
  | ExtArray(x) -> ExtArray(x) |> return
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys) |> return


let f = g M.empty
