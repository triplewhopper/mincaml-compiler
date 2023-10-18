(** translation into assembly with infinite number of virtual registers *)

(* open Asm *)

let data = ref [] (** 浮動小数点数の定数テーブル (caml2html: virtual_data) *)

let classify (xts: (Id.t * Type.t) list) ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
      match t with
      | Type.Unit -> acc
      | Type.Float -> addf acc x
      | _ -> addi acc x t)
    ini
    xts

let separate xts =
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
      let offset = Asm.align offset in
      (offset + 8, addf x offset acc))
    (fun (offset, acc) x t ->
      (offset + 4, addi x t offset acc))

let rec g env cl = let open Asm in
  let return value = { value = value; tokens = cl.Closure.tokens; prev=KNormal.PrevRight cl} in
  let setFather father value = { value = value; tokens = NList.empty; prev=KNormal.Father father} in
  match cl.Closure.value with (** 式の仮想マシンコード生成 (caml2html: virtual_g) *)
  | Closure.Unit -> Ans(Nop) |> return
  | Closure.Int(i) -> Ans(Set(i)) |> return
  | Closure.Float(d) ->
      let l =
        try
          (* すでに定数テーブルにあったら再利用 Cf. https://github.com/esumii/min-caml/issues/13 *)
          let (l, _) = List.find (fun (_, d') -> d = d') !data in
          l
        with Not_found ->
          let l = Id.L(Id.genid_l __LOC__) in
          data := (l, d) :: !data;
          l in
      let x = Id.genid_l __LOC__ in
      let p, r = Promise.make () in 
      let v = return (Asm.Let((x, Type.Int), SetL(l), NList.empty, setFather p (Ans(LdDF(x, C(0), 1))))) in
        Promise.resolve r v; v
  | Closure.Neg(x) -> Ans(Neg(x)) |> return
  | Closure.Add(x, y) -> Ans(Add(x, V(y))) |> return
  | Closure.Sub(x, y) -> Ans(Sub(x, V(y))) |> return
  | Closure.FNeg(x) -> Ans(FNegD(x)) |> return
  | Closure.FAdd(x, y) -> Ans(FAddD(x, y)) |> return
  | Closure.FSub(x, y) -> Ans(FSubD(x, y)) |> return
  | Closure.FMul(x, y) -> Ans(FMulD(x, y)) |> return
  | Closure.FDiv(x, y) -> Ans(FDivD(x, y)) |> return
  | Closure.IfEq(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfEq(x, V(y), g env e1, g env e2)) |> return
      | Type.Float -> Ans(IfFEq(x, y, g env e1, g env e2)) |> return
      | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE(x, y, e1, e2) ->
      (match M.find x env with
      | Type.Bool | Type.Int -> Ans(IfLE(x, V(y), g env e1, g env e2)) |> return
      | Type.Float -> Ans(IfFLE(x, y, g env e1, g env e2)) |> return
      | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.Let((x, t1), e1, e2) ->
      let e1' = g env e1 in
      let e2' = g (M.add x t1 env) e2 in
      Asm.concat e1' (x, t1) e2'
  | Closure.Var(x) ->
      (match M.find x env with
      | Type.Unit -> Ans(Nop)
      | Type.Float -> Ans(FMovD(x))
      | _ -> Ans(Mov(x))) |> return
  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* クロージャの生成 (caml2html: virtual_makecls) *)
      (* Closureのアドレスをセットしてから、自由変数の値をストア *)
      let e2' = g (M.add x t env) e2 in
      let p, r = Promise.make () in
      let offset, store_fv =
        expand
          (List.map (fun y -> (y, M.find y env)) ys) (* すべての自由変数の型 *)
          (4, e2')
          (fun y offset store_fv -> seq(StDF(y, x, C(offset), 1), store_fv) |> setFather p)
          (fun y _ offset store_fv -> seq(St(y, x, C(offset), 1), store_fv) |> setFather p) in
      let v =
      Let((x, t), Mov(Asm.reg_hp), NList.empty,
          Let((Asm.reg_hp, Type.Int), Add(Asm.reg_hp, C(Asm.align offset)), NList.empty,
              let z = Id.genid_l __LOC__ in
              Let((z, Type.Int), SetL(l), NList.empty,
                  Asm.seq(St(z, x, C(0), 1),
                      store_fv)|> setFather p)|> setFather p) |> setFather p) |> return in Promise.resolve r v; v
  | Closure.AppCls(x, ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallCls(x, int, float)) |> return
  | Closure.AppDir(Id.L(x), ys) ->
      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
      Ans(CallDir(Id.L(x), int, float)) |> return
  | Closure.Tuple(xs) -> (* 組の生成 (caml2html: virtual_tuple) *)
      let y = Id.genid_t __LOC__ in
      let p, r = Promise.make () in
      let (offset, store) =
        expand 
          (List.map (fun x -> (x, M.find x env)) xs)
          (0, Asm.Ans(Mov(y)) |> setFather p)
          (fun x offset store -> Asm.seq(StDF(x, y, C(offset), 1), store) |> setFather p)
          (fun x _ offset store -> Asm.seq(St(x, y, C(offset), 1), store) |> setFather p) in
      let v =
      Let((y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Mov(Asm.reg_hp), NList.empty,
          Let((Asm.reg_hp, Type.Int), Add(Asm.reg_hp, C(Asm.align offset)), NList.empty,
              store)|> setFather p) |> return in Promise.resolve r v; v
  | Closure.LetTuple(xts, y, e2) ->
      let s = Closure.fv e2 in
      let p, r = Promise.make () in
      let (offset, load) =
        expand
          xts
          (0, g (M.add_list xts env) e2) 
          (fun x offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            Asm.fletd(x, LdDF(y, C(offset), 1), load) |> setFather p[@ppwarning "which one should p be resolved to? load?"])
          (fun x t offset load ->
            if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
            Let((x, t), Ld(y, C(offset), 1), NList.empty, load) |> setFather p[@ppwarning "which one should p be resolved to? load?"]) in
      Promise.resolve r load;
      {load with tokens = cl.Closure.tokens; prev=KNormal.PrevRight cl}
  | Closure.Get(x, y) -> (* 配列の読み出し (caml2html: virtual_get) *)
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) -> Ans(LdDF(x, V(y), 8))
      | Type.Array(_) -> Ans(Ld(x, V(y), 4))
      | _ -> assert false) |> return
  | Closure.Put(x, y, z) ->
      (match M.find x env with
      | Type.Array(Type.Unit) -> Ans(Nop)
      | Type.Array(Type.Float) -> Ans(StDF(z, x, V(y), 8))
      | Type.Array(_) -> Ans(St(z, x, V(y), 4))
      | _ -> assert false) |> return
  | Closure.ExtArray(Id.L(x)) -> Ans(SetL(Id.L(Id.genid_prefix ~prefix:"min_caml_" x))) |> return

(** 関数の仮想マシンコード生成 (caml2html: virtual_h) *)
let h { Closure.name = (Id.L(x), t); args = yts; formal_fv = zts; body = e; link = kn} =
  let (int, float) = separate yts in
  let p, r = Promise.make () in
  let (offset, load) =
    expand
      zts
      (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> {Asm.value=Asm.fletd(z, LdDF(x, C(offset), 1), load);tokens=NList.empty;prev=KNormal.Father p})
      (fun z t offset load -> {Asm.value=Let((z, t), Ld(x, C(offset), 1), NList.empty, load);tokens=NList.empty;prev=KNormal.Father p}) in
  Promise.resolve r load;
  match t with
  | Type.Fun(_, t2) ->
      { Asm.name = Id.L(x); args = int; fargs = float; body = load; ret = t2; link = kn }
  | _ -> assert false

(** プログラム全体の仮想マシンコード生成 (caml2html: virtual_f) *)
let f (Closure.Prog(fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Asm.Prog(!data, fundefs, e)
