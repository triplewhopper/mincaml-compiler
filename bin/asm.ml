(** 2オペランドではなく3オペランドのx86アセンブリもどき *)

type id_or_imm = V of Id.t | C of int [@@deriving eq]

let pp_id_or_imm ppf: id_or_imm -> unit = function
  | V(x) -> Id.pp ppf x
  | C(i) -> Format.fprintf ppf "$%d" i
type t = { (** 命令の列 (caml2html: sparcasm_t) *)
  value: instr;
  tokens: Token.t NList.t [@equal (==)];
  prev: (t, Closure.t) KNormal.link
  [@equal (==)]
  [@printer fun fmt -> function
    | KNormal.PrevLeft t -> pp fmt t
    | KNormal.PrevRight t -> Closure.pp fmt t
    | KNormal.Father _ -> ()]
} [@@deriving show, eq]
and instr = 
  | Ans of exp (** 単一の命令に対応する式 *)
  | Let of (Id.t * Type.t) * exp * Token.t NList.t * t
and exp = (** 一つ一つの命令に対応する式 (caml2html: sparcasm_exp) *)
  | Nop
  | Set of int
  | SetL of Id.l
  | Mov of Id.t 
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Ld of Id.t * id_or_imm * int
  | St of Id.t * Id.t * id_or_imm * int
  | FMovD of Id.t
  | FNegD of Id.t
  | FAddD of Id.t * Id.t
  | FSubD of Id.t * Id.t
  | FMulD of Id.t * Id.t
  | FDivD of Id.t * Id.t
  | LdDF of Id.t * id_or_imm * int
  | StDF of Id.t * Id.t * id_or_imm * int
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t (* 左右対称ではないので必要 *)
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 (caml2html: sparcasm_save) *)
  | Restore of Id.t (* スタック変数から値を復元 (caml2html: sparcasm_restore) *)
type fundef = { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t; link: KNormal.t}

(** プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
type prog = Prog of (Id.l * float) list * fundef list * t

let fletd(x, e1, e2) = Let((x, Type.Float), e1, NList.empty, e2)
let seq(e1, e2) = Let((Id.gentmp Type.Unit __LOC__, Type.Unit), e1, NList.empty, e2)

let regs = (* Array.init 16 (fun i -> Printf.sprintf "%%r%d" i) *)
  Array.map Id.makeRegister [| "%eax"; "%ebx"; "%ecx"; "%edx"; "%esi"; "%edi" |]
let fregs = Array.init 8 (fun i -> Printf.sprintf "%%xmm%d" i |> Id.makeRegister)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address (caml2html: sparcasm_regcl) *)
(*
let reg_sw = regs.(Array.length regs - 1) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
*)
let reg_sp = Id.makeRegister "%ebp" (** stack pointer *)

let reg_hp = Id.makeRegister "min_caml_hp" (** heap pointer (caml2html: sparcasm_reghp) *)
(* let reg_ra = "%eax" (* return address *) *)
(* let is_reg x = (x.[0] = '%' || x = reg_hp) *)
let is_reg x = Id.isRegister x || x = reg_hp

(** super-tenuki *)
let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(** free variables in the order of use (for spilling) (caml2html: sparcasm_fv) *)
let fv_id_or_imm = function V(x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop | Set(_) | SetL(_) | Comment(_) | Restore(_) -> []
  | Mov(x) | Neg(x) | FMovD(x) | FNegD(x) | Save(x, _) -> [x]
  | Add(x, y') | Sub(x, y') | Ld(x, y', _) | LdDF(x, y', _) -> x :: fv_id_or_imm y'
  | St(x, y, z', _) | StDF(x, y, z', _) -> x :: y :: fv_id_or_imm z'
  | FAddD(x, y) | FSubD(x, y) | FMulD(x, y) | FDivD(x, y) -> [x; y]
  | IfEq(x, y', e1, e2) | IfLE(x, y', e1, e2) | IfGE(x, y', e1, e2) -> x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | IfFEq(x, y, e1, e2) | IfFLE(x, y, e1, e2) -> x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
  | CallCls(x, ys, zs) -> x :: ys @ zs
  | CallDir(_, ys, zs) -> ys @ zs
and fv asm = match asm.value with
  | Ans(exp) -> fv_exp exp
  | Let((x, t), exp, _, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)
let fv e = remove_and_uniq S.empty (fv e)

let rec concat e1 xt e2 =
  match e1.value with
  | Ans(exp) -> {value=Let(xt, exp, e1.tokens, e2); tokens=NList.concat e1.tokens e2.tokens; prev=KNormal.PrevLeft e1}
  | Let(yt, exp, tk, e1') -> {value=Let(yt, exp, tk, concat e1' xt e2); tokens=NList.concat e1.tokens e2.tokens; prev=KNormal.PrevLeft e1}

let align i = (if i mod 8 = 0 then i else i + 4)

let return_t t instr: t = {t with value=instr; prev=KNormal.PrevLeft t}

let setFather father t: t = {t with tokens=NList.empty;prev=KNormal.Father father}