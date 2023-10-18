(** give names to intermediate values (K-normalization) *)
type ('a, 'b) link = PrevLeft of 'a | PrevRight of 'b | Father of 'a Promise.t
type t = {(** K正規化後の式 (caml2html: knormal_t) *)
  value: exp;
  tokens: Token.t NList.t[@equal (==)];
  prev: (t, Syntax.ast) link
  [@printer fun fmt -> function PrevLeft t -> pp fmt t | PrevRight t -> Syntax.pp_ast fmt t | Father _ -> ()]
  [@equal (==)];
} and exp = 
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t (* 比較 + 分岐 (caml2html: knormal_branch) *)
  | IfLE of Id.t * Id.t * t * t (* 比較 + 分岐 *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtFunApp of Id.t * Id.t list [@@deriving show,eq]
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let shallowEq kn1 kn2 = equal_exp kn1.value kn2.value
let rec fv kn = match kn.value with (** 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  | Unit | Int(_) | Float(_) | ExtArray(_) -> S.empty
  | Neg(x) | FNeg(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, _t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = S.diff (fv e1) (S.of_list (List.map fst yts)) in
      S.diff (S.union zs (fv e2)) (S.singleton x)
  | App(x, ys) -> S.of_list (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> S.of_list xs
  | Put(x, y, z) -> S.of_list [x; y; z]
  | LetTuple(xs, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xs)))

let insert_let (kn, t) k = (** letを挿入する補助関数 (caml2html: knormal_insert) *)
  match kn.value with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t __LOC__ in
      let kn', t' = k x in 
      {value=Let((x, t), kn, kn');tokens=kn.tokens;prev=PrevLeft(kn)}, t'

let rec g env (ast: Syntax.ast): t * Type.t = (** K正規化ルーチン本体 (caml2html: knormal_g) *)
  let makePrevAst ?(prev=ast) x = Syntax.makeAstWithPrev ~prev x in
  let makeKNormal exp = {value=exp;tokens=ast.tokens;prev=PrevRight(ast)} in
  match ast.value with 
  | Syntax.Unit -> makeKNormal Unit, Type.Unit
  | Syntax.Bool(b) -> makeKNormal (Int(if b then 1 else 0)), Type.Int (* 論理値true, falseを整数1, 0に変換 (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> makeKNormal (Int(i)), Type.Int
  | Syntax.Float(d) -> makeKNormal (Float(d)), Type.Float
  | Syntax.Not(e) -> let b x = Syntax.makeAstWithFather ~father:ast (Syntax.Bool(x)) in g env (makePrevAst (Syntax.If(e, (b false), (b true))))
  | Syntax.Neg(e) ->
      insert_let (g env e)
        (fun x -> makeKNormal(Neg(x)), Type.Int)
  | Syntax.Add(e1, e2) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(Add(x, y)), Type.Int))
  | Syntax.Sub(e1, e2) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(Sub(x, y)), Type.Int))
  | Syntax.FNeg(e) ->
      insert_let (g env e)
        (fun x -> makeKNormal(FNeg(x)), Type.Float)
  | Syntax.FAdd(e1, e2) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(FAdd(x, y)), Type.Float))
  | Syntax.FSub(e1, e2) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(FSub(x, y)), Type.Float))
  | Syntax.FMul(e1, e2) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(FMul(x, y)), Type.Float))
  | Syntax.FDiv(e1, e2) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> makeKNormal(FDiv(x, y)), Type.Float))
  | Syntax.Eq _ | Syntax.Neq _ | Syntax.LE _ | Syntax.GE _ | Syntax.LT _ | Syntax.GT _->
      let b x = Syntax.makeAstWithFather ~father:ast (Syntax.Bool(x)) in
      g env (makePrevAst (Syntax.If(ast, (b true), (b false))))
  | Syntax.If(({value=Syntax.Not(e1);_}), e2, e3)  -> g env (makePrevAst (Syntax.If(e1, e3, e2))) (* notによる分岐を変換 (caml2html: knormal_not) *)
  | Syntax.If(({value=Syntax.Eq(e1, e2);_}), e3, e4)  ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y ->
              let e3', t3 = g env e3 in
              let e4', _t4 = g env e4 in
              makeKNormal(IfEq(x, y, e3', e4')), t3))
  | Syntax.If(({value=Syntax.Neq(e1, e2);_}), e3, e4) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y ->
              let e3', t3 = g env e3 in
              let e4', _t4 = g env e4 in
              makeKNormal(IfEq(x, y, e4', e3')), t3))
  | Syntax.If(({value=(Syntax.LE(e1, e2)|Syntax.GE(e2, e1));_}), e3, e4) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y ->
              let e3', t3 = g env e3 in
              let e4', _t4 = g env e4 in
              makeKNormal(IfLE(x, y, e3', e4')), t3))
  | Syntax.If(({value=(Syntax.LT(e1, e2)|Syntax.GT(e2, e1));_}), e3, e4) -> 
      (* if e1 < e2 then e3 else e4
      if !(e1 >= e2) then e3 else e4
      if !(e2 <= e1) then e3 else e4
      if e2 <= e1 then e4 else e3 *)
      insert_let (g env e1)
          (fun x -> insert_let (g env e2)
            (fun y ->
              let e3', t3 = g env e3 in
              let e4', _t4 = g env e4 in
              makeKNormal(IfLE(y, x, e4', e3')), t3))
  | Syntax.If(e1, e2, e3) -> 
    let bf = Syntax.makeAstWithFather ~father:ast (Syntax.Bool(false)) in 
    g env (makePrevAst (Syntax.If(makePrevAst ~prev:e1 (Syntax.Eq(e1, bf)), e3, e2))) (* 比較のない分岐を変換 (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
      let e1', _t1 = g env e1 in
      let e2', t2 = g (M.add x t env) e2 in
      makeKNormal(Let((x, t), e1', e2')), t2
  | Syntax.Var(x) when M.mem x env -> makeKNormal(Var(x)), M.find x env
  | Syntax.Var(x) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
      (match M.find x !Typing.extenv with
      | Type.Array(_) as t -> makeKNormal(ExtArray x), t
      | _ -> failwith (Format.fprintf Format.str_formatter "@[external variable@ @[%a@]@ does not have an array type@]@." Id.pp x;
        Format.flush_str_formatter ()))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
      let env' = M.add x t env in
      let e2', t2 = g env' e2 in
      let e1', _t1 = g (M.add_list yts env') e1 in
      makeKNormal(LetRec({ name = (x, t); args = yts; body = e1' }, e2')), t2
  | Syntax.App({value=Syntax.Var(f);_}, e2s) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
      (match M.find f !Typing.extenv with
      | Type.Fun(_, t) ->
          let rec bind xs = function (* "xs" are identifiers for the arguments *)
            | [] -> makeKNormal(ExtFunApp(f, xs)), t
            | e2 :: e2s ->
                insert_let (g env e2)
                  (fun x -> bind (xs @ [x]) e2s) in
          bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(e1, e2s) ->
      (match g env e1 with
      | _, Type.Fun(_, t) as g_e1 ->
          insert_let g_e1
            (fun f ->
              let rec bind xs = function (* "xs" are identifiers for the arguments *)
                | [] -> makeKNormal(App(f, xs)), t
                | e2 :: e2s ->
                    insert_let (g env e2)
                      (fun x -> bind (xs @ [x]) e2s) in
              bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
        | [] -> makeKNormal(Tuple(xs)), Type.Tuple(ts)
        | e :: es ->
            let _, t as g_e = g env e in
            insert_let g_e
              (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
      bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
      insert_let (g env e1)
        (fun y ->
          let e2', t2 = g (M.add_list xts env) e2 in
          makeKNormal(LetTuple(xts, y, e2')), t2)
  | Syntax.Array(e1, e2) ->
      insert_let (g env e1)
        (fun x ->
          let _, t2 as g_e2 = g env e2 in
          insert_let g_e2
            (fun y ->
              let l' =
                match t2 with
                | Type.Float -> "create_float_array"
                | _ -> "create_array" in 
                let l = Id.makeExternal ~name:l' ~origin:(NList.find_opt (fun Token.{text;_} -> "Array.make" = text || "Array.create" = text) ast.tokens |> Option.get) in
              makeKNormal(ExtFunApp(l, [x; y])), Type.Array(t2)))
  | Syntax.Get(e1, e2) ->
      (match g env e1 with
      |        _, Type.Array(t) as g_e1 ->
          insert_let g_e1
            (fun x -> insert_let (g env e2)
                (fun y -> makeKNormal(Get(x, y)), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3) ->
      insert_let (g env e1)
        (fun x -> insert_let (g env e2)
            (fun y -> insert_let (g env e3)
                (fun z -> makeKNormal(Put(x, y, z)), Type.Unit)))


let f e = fst (g M.empty e)
