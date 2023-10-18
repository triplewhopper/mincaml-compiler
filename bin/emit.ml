(* open Asm *)

let gethi x = Int64.bits_of_float x |> Int64.logand 0xffffffffL |> Int64.to_int32 (* external gethi : float -> int32 = "gethi" *)
let getlo x = Int64.shift_right_logical (Int64.bits_of_float x) 32 |> Int64.to_int32 (* external getlo : float -> int32 = "getlo" *)

let stackset = ref S.empty (** すでにSaveされた変数の集合 (caml2html: emit_stackset) *)

let stackmap = ref [] (** Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
let save x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad =
      if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int __LOC__] in
    stackmap := !stackmap @ pad @ [x; x])
let locate x = 
  let rec loc = function
    | [] -> []
    | y :: zs when Id.equal x y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  (* Printf.eprintf "locate %s\n" (Id.toString x); *)
  loc !stackmap
let offset x = 4 * List.hd (locate x)
let stacksize () = Asm.align (List.length !stackmap * 4)

(* let pp_id_or_imm = function
  | Asm.V(x) -> Format.fprintf Format.str_formatter "%a" Id.pp x; Format.flush_str_formatter ()
  | C(i) -> "$" ^ string_of_int i *)

(** 関数呼び出しのために引数を並べ替える(register shuffling) (caml2html: emit_shuffle) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> Id.equal x y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
      (y, sw) :: (x, y) :: shuffle sw (List.map
                                         (function
                                           | (y', z) when Id.equal y y' -> (sw, z)
                                           | yz -> yz)
                                         xys)
  | xys, acyc -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (** 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)

let movl oc ~src ~dest = Format.fprintf oc "\tmovl\t%a, %a@." Id.pp src Id.pp dest
let movl_imm oc ~imm ~dest = Format.fprintf oc "\tmovl\t$%d, %a@." imm Id.pp dest
let movl_label oc ~src:(Id.L(l)) ~dest = Format.fprintf oc "\tmovl\t$%a, %a@." Id.pp l Id.pp dest
let movl_from_base_index_scale oc ~base ~index ~scale ~dest = Format.fprintf oc "\tmovl\t(%a,%a,%d), %a@." Id.pp base Id.pp index scale Id.pp dest
let movl_from_offset_base oc ~offset ~base ~dest = Format.fprintf oc "\tmovl\t%d(%a), %a@." offset Id.pp base Id.pp dest
let movl_to_base_index_scale oc ~src ~base ~index ~scale = Format.fprintf oc "\tmovl\t%a, (%a,%a,%d)@." Id.pp src Id.pp base Id.pp index scale
let movl_to_offset_base oc ~src ~offset ~base = Format.fprintf oc "\tmovl\t%a, %d(%a)@." Id.pp src offset Id.pp base
let movsd oc ~src ~dest = Format.fprintf oc "\tmovsd\t%a, %a@." Id.pp src Id.pp dest
let movsd_from_base_index_scale oc ~base ~index ~scale ~dest = Format.fprintf oc "\tmovsd\t(%a,%a,%d), %a@." Id.pp base Id.pp index scale Id.pp dest
let movsd_from_offset_base oc ~offset ~base ~dest = Format.fprintf oc "\tmovsd\t%d(%a), %a@." offset Id.pp base Id.pp dest
let movsd_to_base_index_scale oc ~src ~base ~index ~scale = Format.fprintf oc "\tmovsd\t%a, (%a,%a,%d)@." Id.pp src Id.pp base Id.pp index scale
let movsd_to_offset_base oc ~src ~offset ~base = Format.fprintf oc "\tmovsd\t%a, %d(%a)@." Id.pp src offset Id.pp base
let negl oc ~inplace = Format.fprintf oc "\tnegl\t%a@." Id.pp inplace
let xorpd_min_caml_fnegd oc ~dest = Format.fprintf oc "\txorpd\tmin_caml_fnegd, %a@." Id.pp dest
let addl oc ~src ~dest = Format.fprintf oc "\taddl\t%a, %a@." Id.pp src Id.pp dest
let addl_imm oc ~imm ~dest = Format.fprintf oc "\taddl\t$%d, %a@." imm Id.pp dest
let addl_id_or_imm oc ~src ~dest = Format.fprintf oc "\taddl\t%a, %a@." Asm.pp_id_or_imm src Id.pp dest
let addsd oc ~src ~dest = Format.fprintf oc "\taddsd\t%a, %a@." Id.pp src Id.pp dest
let subl oc ~src ~dest = Format.fprintf oc "\tsubl\t%a, %a@." Id.pp src Id.pp dest
let subl_imm oc ~imm ~dest = Format.fprintf oc "\tsubl\t$%d, %a@." imm Id.pp dest
let subl_id_or_imm oc ~src ~dest = Format.fprintf oc "\tsubl\t%a, %a@." Asm.pp_id_or_imm src Id.pp dest
let subsd oc ~src ~dest = Format.fprintf oc "\tsubsd\t%a, %a@." Id.pp src Id.pp dest
let subsd_from_offset_base oc ~offset ~base ~dest = Format.fprintf oc "\tsubsd\t%d(%a), %a@." offset Id.pp base Id.pp dest
let mulsd oc ~src ~dest = Format.fprintf oc "\tmulsd\t%a, %a@." Id.pp src Id.pp dest
let divsd oc ~src ~dest = Format.fprintf oc "\tdivsd\t%a, %a@." Id.pp src Id.pp dest
let divsd_from_offset_base oc ~offset ~base ~dest = Format.fprintf oc "\tdivsd\t%d(%a), %a@." offset Id.pp base Id.pp dest
let ret oc = Format.fprintf oc "\tret@."
let call oc ~label = Format.fprintf oc "\tcall\t*(%a)\t# %a@." Id.pp label Id.pp_id label
let rec print_loc ?(vis=10) oc tokens (prev: (Asm.t, Closure.t) KNormal.link) =
  let print_token_lnum (token: Token.t) = Format.fprintf oc "# line %d@." token.start.pos_lnum in
  let rec print_ast_loc vis oc tokens (prev: Syntax.ast option) =
    (if NList.is_empty tokens && vis > 0 then match prev with
      | None -> ()
      | Some ast -> print_ast_loc (vis-1) oc ast.tokens ast.prev
  else NList.front tokens |> Option.fold ~some:print_token_lnum ~none:()) in
  let rec print_kn_loc vis oc tokens (prev: (KNormal.t, Syntax.ast) KNormal.link) =
    (if NList.is_empty tokens && vis > 0 then match prev with
      | KNormal.PrevLeft kn -> print_kn_loc (vis-1) oc kn.tokens kn.prev
      | KNormal.PrevRight ast -> print_ast_loc (vis-1) oc ast.tokens ast.prev
      | KNormal.Father p -> match Promise.state p with 
        | Promise.Pending -> assert false
        | Promise.Resolved kn -> print_kn_loc (vis-1) oc kn.tokens kn.prev
  else NList.front tokens |> Option.fold ~some:print_token_lnum ~none:()) in
  let rec print_cl_loc vis oc tokens (prev: (Closure.t, (KNormal.t, Syntax.ast) Either.t) Either.t) = 
    (if NList.is_empty tokens && vis > 0 then match prev with
      | Either.Left cl -> print_cl_loc (vis-1) oc cl.tokens cl.prev
      | Either.Right (Either.Left kn) -> print_kn_loc (vis-1) oc kn.tokens kn.prev
      | Either.Right (Either.Right ast) -> print_ast_loc (vis-1) oc ast.tokens ast.prev
  else NList.front tokens |> Option.fold ~some:print_token_lnum ~none:())
  in 
  if NList.is_empty tokens && vis > 0 then match prev with
    | KNormal.PrevLeft asm -> print_loc ~vis:(vis-1) oc asm.tokens asm.prev
    | KNormal.PrevRight cl -> print_cl_loc (vis-1) oc cl.tokens cl.prev
    | KNormal.Father p -> match Promise.state p with 
      | Promise.Pending -> assert false
      | Promise.Resolved asm -> assert (asm.prev != prev); print_loc ~vis:(vis-1) oc asm.tokens asm.prev
else NList.front tokens |> Option.fold ~some:print_token_lnum ~none:()


(** 命令列のアセンブリ生成 (caml2html: emit) *)
let rec g oc = function (** 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, {Asm.value=Asm.Ans(exp);tokens;prev} -> g' oc tokens prev (dest, exp)
  | dest, {Asm.value=Let((x, t), exp, tk, e);tokens=_; prev} ->
      g' oc tk prev (NonTail(x), exp);
      g oc (dest, e)

(** 各命令のアセンブリ生成 (caml2html: emit_gprime)

    末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
and g' oc tokens prev (dest, exp)= 
  (match dest, exp with _, Nop | Tail, _ -> () | _ -> print_loc oc tokens prev);
  match dest, exp with
  | NonTail(_), Nop -> ()
  | NonTail(x), Set(i) -> movl_imm oc i x
  | NonTail(x), SetL(Id.L(y)) -> movl_label oc ~src:(Id.L(y)) ~dest:x
  | NonTail(x), Mov(y) ->
      if not Id.(equal x y) then movl oc y x
  | NonTail(x), Neg(y) ->
      if not Id.(equal x y) then movl oc y x;
      negl oc x
  | NonTail(x), Add(y, z') ->
      if match z' with V(z'') when Id.equal z'' x -> true | _ -> false then
        addl oc y x
      else
        (if not Id.(equal x y) then movl oc y x;
         addl_id_or_imm oc ~src:z' ~dest:x)
  | NonTail(x), Sub(y, z') ->
      if match z' with V(z'') when Id.equal z'' x -> true | _ -> false then
        (subl oc y x;
         negl oc x)
      else
        (if not Id.(equal x y) then movl oc y x;
         subl_id_or_imm oc ~src:z' ~dest:x)
  | NonTail(x), Ld(y, V(z), i) -> movl_from_base_index_scale oc y z i x [@warning "-6"]
  | NonTail(x), Ld(y, C(j), i) -> movl_from_offset_base oc (j * i) y x [@warning "-6"]
  | NonTail(_), St(x, y, V(z), i) -> movl_to_base_index_scale oc x y z i [@warning "-6"]
  | NonTail(_), St(x, y, C(j), i) -> movl_to_offset_base oc x (j * i) y [@warning "-6"]
  | NonTail(x), FMovD(y) ->
      if not Id.(equal x y) then print_loc oc tokens prev; movsd oc y x
  | NonTail(x), FNegD(y) ->
      if not Id.(equal x y) then movsd oc y x;
      xorpd_min_caml_fnegd oc ~dest:x
  | NonTail(x), FAddD(y, z) ->
      if Id.equal x z then
        addsd oc y x
      else
        (if not Id.(equal x y) then movsd oc y x;
         addsd oc z x)
  | NonTail(x), FSubD(y, z) ->
      if Id.equal x z then (* [XXX] ugly *)
        let ss = stacksize () in
        movsd_to_offset_base oc z ss Asm.reg_sp;
        if not Id.(equal x y) then movsd oc y x;
        subsd_from_offset_base oc ss Asm.reg_sp x
      else
        (if not Id.(equal x y) then movsd oc y x;
         subsd oc z x)
  | NonTail(x), FMulD(y, z) ->
      if Id.equal x z then
        mulsd oc y x
      else
        (if not Id.(equal x y) then movsd oc y x;
          mulsd oc z x)
  | NonTail(x), FDivD(y, z) ->
      if Id.equal x z then (* [XXX] ugly *)
        let ss = stacksize () in
        movsd_to_offset_base oc z ss Asm.reg_sp;
        if not Id.(equal x y) then movsd oc y x;
        divsd_from_offset_base oc ss Asm.reg_sp x
      else
        (if not Id.(equal x y) then movsd oc y x;
         divsd oc z x)
  | NonTail(x), LdDF(y, V(z), i) -> movsd_from_base_index_scale oc y z i x
  | NonTail(x), LdDF(y, C(j), i) -> movsd_from_offset_base oc (j * i) y x
  | NonTail(_), StDF(x, y, V(z), i) -> movsd_to_base_index_scale oc x y z i
  | NonTail(_), StDF(x, y, C(j), i) -> movsd_to_offset_base oc x (j * i) y
  | NonTail(_), Comment(s) -> assert (not (String.contains s '\n')); print_loc oc tokens prev; Format.fprintf oc "\t# %s@." s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x Asm.allregs && not (S.mem y !stackset) ->
      save y;
      movl_to_offset_base oc x (offset y) Asm.reg_sp
  | NonTail(_), Save(x, y) when List.mem x Asm.allfregs && not (S.mem y !stackset) ->
      savef y;
      movsd_to_offset_base oc x (offset y) Asm.reg_sp
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x Asm.allregs ->
      movl_from_offset_base oc (offset y) Asm.reg_sp x
  | NonTail(x), Restore(y) ->
      assert (List.mem x Asm.allfregs);
      movsd_from_offset_base oc (offset y) Asm.reg_sp x
  (* 末尾だったら計算結果を第一レジスタにセットしてret (caml2html: emit_tailret) *)
  | Tail, (Nop | St _ | StDF _ | Comment _ | Save _ as exp) ->
      g' oc tokens prev (NonTail(Id.gentmp Type.Unit __LOC__), exp);
      ret oc
  | Tail, (Set _ | SetL _ | Mov _ | Neg _ | Add _ | Sub _ | Ld _ as exp) ->
      g' oc tokens prev (NonTail(Asm.regs.(0)), exp);
      ret oc
  | Tail, (FMovD _ | FNegD _ | FAddD _ | FSubD _ | FMulD _ | FDivD _ | LdDF _  as exp) ->
      g' oc tokens prev (NonTail(Asm.fregs.(0)), exp);
      ret oc
  | Tail, (Restore(x) as exp) ->
      (match locate x with
      | [i] -> g' oc tokens prev (NonTail(Asm.regs.(0)), exp)
      | [i; j] when i + 1 = j -> g' oc tokens prev (NonTail(Asm.fregs.(0)), exp)
      | _ -> assert false);
      ret oc
  | Tail, IfEq(x, y', e1, e2) ->
      print_loc oc tokens prev;
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_tail_if oc e1 e2 Id.JE Id.JNE
  | Tail, IfLE(x, y', e1, e2) ->
      print_loc oc tokens prev;
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_tail_if oc e1 e2 Id.JLE Id.JG
  | Tail, IfGE(x, y', e1, e2) ->
      print_loc oc tokens prev;
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_tail_if oc e1 e2 Id.JGE Id.JL
  | Tail, IfFEq(x, y, e1, e2) ->
      print_loc oc tokens prev;
      Format.fprintf oc "\tcomisd\t%a, %a@." Id.pp y Id.pp x;
      g'_tail_if oc e1 e2 Id.JE Id.JNE
  | Tail, IfFLE(x, y, e1, e2) ->
      Format.fprintf oc "\tcomisd\t%a, %a@." Id.pp y Id.pp x;
      g'_tail_if oc e1 e2 Id.JBE Id.JA
  | NonTail(z), IfEq(x, y', e1, e2) ->
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 Id.JE Id.JNE
  | NonTail(z), IfLE(x, y', e1, e2) ->
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 Id.JLE Id.JG
  | NonTail(z), IfGE(x, y', e1, e2) ->
      Format.fprintf oc "\tcmpl\t%a, %a@." Asm.pp_id_or_imm y' Id.pp x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 Id.JGE Id.JL
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      Format.fprintf oc "\tcomisd\t%a, %a@." Id.pp y Id.pp x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 Id.JE Id.JNE
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      Format.fprintf oc "\tcomisd\t%a, %a@." Id.pp y Id.pp x;
      g'_non_tail_if oc (NonTail(z)) e1 e2 Id.JBE Id.JA
  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
      print_loc oc tokens prev;
      g'_args oc [(x, Asm.reg_cl)] ys zs;
      Format.fprintf oc "\tjmp \t*(%a)@." Id.pp Asm.reg_cl;
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      print_loc oc tokens prev;
      g'_args oc [] ys zs;
      Format.fprintf oc "\tjmp \t%a@." Id.pp x;
  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args oc [(x, Asm.reg_cl)] ys zs;
      let ss = stacksize () in
      if ss > 0 then addl_imm oc ~imm:ss ~dest:Asm.reg_sp;
      call oc ~label:Asm.reg_cl;
      if ss > 0 then subl_imm oc ~imm:ss ~dest:Asm.reg_sp;
      if List.mem a Asm.allregs && not Id.(equal a Asm.regs.(0)) then
        movl oc ~src:Asm.regs.(0) ~dest:a
      else if List.mem a Asm.allfregs && not Id.(equal a Asm.fregs.(0)) then
        movsd oc ~src:Asm.fregs.(0) ~dest:a
  | NonTail(a), CallDir(Id.L(x), ys, zs) ->
      g'_args oc [] ys zs;
      let ss = stacksize () in
      if ss > 0 then addl_imm oc ~imm:ss ~dest:Asm.reg_sp;
      call oc ~label:x;
      if ss > 0 then subl_imm oc ~imm:ss ~dest:Asm.reg_sp;
      if List.mem a Asm.allregs && not (Id.equal a Asm.regs.(0)) then
        movl oc ~src:Asm.regs.(0) ~dest:a
      else if List.mem a Asm.allfregs && not (Id.equal a Asm.regs.(0)) then
        movsd oc ~src:Asm.fregs.(0) ~dest:a
and g'_tail_if oc e1 e2 b bn =
  let b_else = Id.genElse b in
  Format.fprintf oc "\t%a\t%a@." Id.pp_cmp bn Id.pp b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Format.fprintf oc "%a:@." Id.pp b_else;
  stackset := stackset_back;
  g oc (Tail, e2);
and g'_non_tail_if oc dest e1 e2 b bn =
  let b_else = Id.genElse b in
  let b_cont = Id.genCont b in
  Format.fprintf oc "\t%a\t%a@." Id.pp_cmp bn Id.pp b_else; 
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Format.fprintf oc "\tjmp \t%a@." Id.pp b_cont;
  Format.fprintf oc "%a:@." Id.pp b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Format.fprintf oc "%a:@." Id.pp b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs =
  assert (List.length ys <= Array.length Asm.regs - List.length x_reg_cl);
  assert (List.length zs <= Array.length Asm.fregs);
  let sw = Id.blackMagic ~offset:(stacksize ()) ~base_reg:Asm.reg_sp in
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, Asm.regs.(i)) :: yrs))
      (0, x_reg_cl)
      ys in
  List.iter
    (fun (y, r) -> Format.fprintf oc "\tmovl\t%a, %a@." Id.pp y Id.pp r)
    (shuffle sw yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, Asm.fregs.(d)) :: zfrs))
      (0, [])
      zs in
  List.iter
    (fun (z, fr) -> Format.fprintf oc "\tmovsd\t%a, %a@." Id.pp z Id.pp fr)
    (shuffle sw zfrs)

let h oc { Asm.name = Id.L(x); args = _; fargs = _; body = e; ret = _ ; link = _} =
  Format.fprintf oc "%s: # %a@," (Id.toString x) Id.pp x;
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Asm.Prog(data, fundefs, e)) =
  let oc = Format.formatter_of_out_channel oc in
  Format.eprintf "generating assembly...@.";
  Format.fprintf oc ".data@.";
  Format.fprintf oc ".balign 8@.";
  List.iter
    (fun (Id.L(x), d) ->
      Format.fprintf oc "%a: # %f@." Id.pp x d;
      Format.fprintf oc "\t.long 0x%lx@." (gethi d);
      Format.fprintf oc "\t.long 0x%lx@." (getlo d))
    data;
  Format.fprintf oc ".text@.";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Format.fprintf oc ".globl min_caml_start@.";
  Format.fprintf oc "min_caml_start:@.";
  Format.fprintf oc ".globl _min_caml_start@.";
  Format.fprintf oc "_min_caml_start: # for cygwin@.";
  Format.fprintf oc "\tpushl\t%%eax@.";
  Format.fprintf oc "\tpushl\t%%ebx@.";
  Format.fprintf oc "\tpushl\t%%ecx@.";
  Format.fprintf oc "\tpushl\t%%edx@.";
  Format.fprintf oc "\tpushl\t%%esi@.";
  Format.fprintf oc "\tpushl\t%%edi@.";
  Format.fprintf oc "\tpushl\t%%ebp@.";
  Format.fprintf oc "\tmovl\t32(%%esp),%a@." Id.pp Asm.reg_sp;
  Format.fprintf oc "\tmovl\t36(%%esp),%a@." Id.pp Asm.regs.(0);
  Format.fprintf oc "\tmovl\t%a, %a@." Id.pp Asm.regs.(0) Id.pp Asm.reg_hp;
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail(Asm.regs.(0)), e);
  Format.fprintf oc "\tpopl\t%%ebp@.";
  Format.fprintf oc "\tpopl\t%%edi@.";
  Format.fprintf oc "\tpopl\t%%esi@.";
  Format.fprintf oc "\tpopl\t%%edx@.";
  Format.fprintf oc "\tpopl\t%%ecx@.";
  Format.fprintf oc "\tpopl\t%%ebx@.";
  Format.fprintf oc "\tpopl\t%%eax@.";

