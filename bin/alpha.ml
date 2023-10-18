(** rename identifiers to make them unique (alpha-conversion) *)

(* open KNormal *)

let find x env = try M.find x env with Not_found -> x

let rec g env kn = 
  let open KNormal in
  let return kn value = if equal_exp value kn.value then kn else { kn with value = value; prev=PrevLeft kn} in
  match kn.value with (** α変換ルーチン本体 (caml2html: alpha_g) *)
  | Unit -> Unit |> return kn
  | Int(i) -> Int(i) |> return kn
  | Float(d) -> Float(d) |> return kn
  | Neg(x) -> Neg(find x env) |> return kn
  | Add(x, y) -> Add(find x env, find y env) |> return kn
  | Sub(x, y) -> Sub(find x env, find y env) |> return kn
  | FNeg(x) -> FNeg(find x env) |> return kn
  | FAdd(x, y) -> FAdd(find x env, find y env) |> return kn
  | FSub(x, y) -> FSub(find x env, find y env) |> return kn
  | FMul(x, y) -> FMul(find x env, find y env) |> return kn
  | FDiv(x, y) -> FDiv(find x env, find y env) |> return kn
  | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, g env e1, g env e2) |> return kn
  | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, g env e1, g env e2) |> return kn
  | Let((x, t), e1, e2) -> (** letのα変換 (caml2html: alpha_let) *)
      let x' = Id.genid x in
      Let((x', t), g env e1, g (M.add x x' env) e2) |> return kn
  | Var(x) -> Var(find x env) |> return kn
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (** let recのα変換 (caml2html: alpha_letrec) *)
      let env = M.add x (Id.genid x) env in
      let ys = List.map fst yts in
      let env' = M.add_list2 ys (List.map Id.genid ys) env in
      LetRec({ name = (find x env, t);
               args = List.map (fun (y, t) -> (find y env', t)) yts;
               body = g env' e1 },
             g env e2) |> return kn
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys) |> return kn
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs) |> return kn
  | LetTuple(xts, y, e) -> (** LetTupleのα変換 (caml2html: alpha_lettuple) *)
      let xs = List.map fst xts in
      let env' = M.add_list2 xs (List.map Id.genid xs) env in
      LetTuple(List.map (fun (x, t) -> (find x env', t)) xts,
               find y env,
               g env' e) |> return kn
  | Get(x, y) -> Get(find x env, find y env) |> return kn
  | Put(x, y, z) -> Put(find x env, find y env, find z env) |> return kn
  | ExtArray(x) -> ExtArray(x) |> return kn
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys) |> return kn


let f = g M.empty
