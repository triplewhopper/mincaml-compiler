open KNormal

let memi x env =
  try (match (M.find x env).value with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match (M.find x env).value with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match (M.find x env).value with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let findi x env = (match M.find x env with {value=Int(i);_} -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with {value=Float(d);_} -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with {value=Tuple(ys);_} -> ys | _ -> raise Not_found)

let rec g env kn = 
  let return value = if equal_exp value kn.value then kn else { kn with value; prev = PrevLeft(kn)} in
  match kn.value with (** 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env) |> return
  (* | Var(x) when memf x env -> Float(findf x env) *)
  (* | Var(x) when memt x env -> Tuple(findt x env) *)
  | Neg(x) when memi x env -> Int(-(findi x env)) |> return
  | Add(x, y) when memi x env && memi y env -> Int(findi x env + findi y env) |> return (* 足し算のケース (caml2html: constfold_add) *)
  | Sub(x, y) when memi x env && memi y env -> Int(findi x env - findi y env) |> return
  | FNeg(x) when memf x env -> Float(-.(findf x env)) |> return
  | FAdd(x, y) when memf x env && memf y env -> Float(findf x env +. findf y env) |> return
  | FSub(x, y) when memf x env && memf y env -> Float(findf x env -. findf y env) |> return
  | FMul(x, y) when memf x env && memf y env -> Float(findf x env *. findf y env) |> return
  | FDiv(x, y) when memf x env && memf y env -> Float(findf x env /. findf y env) |> return
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2) |> return
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2) |> return
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
      let e1' = g env e1 in
      let e2' = g (M.add x e1' env) e2 in
      Let((x, t), e1', e2') |> return
  | LetRec({ name = x; args = ys; body = e1 }, e2) ->
      LetRec({ name = x; args = ys; body = g env e1 }, g env e2) |> return
  | LetTuple(xts, y, e) when memt y env ->
      let p, r = Promise.make () in
      List.fold_left2
        (fun e' xt z -> {value=Let(xt,{value=Var(z);tokens=NList.empty;prev=Father p}, e');tokens=NList.empty;prev=Father p})
        (g env e)
        xts
        (findt y env) |> (fun kn' -> Promise.resolve r kn'; {kn' with tokens=kn.tokens;prev = PrevLeft(kn)})
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e) |> return
  | _e -> kn

let f = g M.empty
