type k = A of Token.t | B of string | External of Token.t | Register | Label | MemoryAddress
[@@deriving show]

type t = string * k * (unit -> unit)
(** 変数の名前 (caml2html: id_t) *)

let pp_id ppf : t -> unit = function
  | _, A token, _ -> Token.pp ppf token
  | id, B loc, _ -> Format.fprintf ppf "@[<h 0>//tmp//%s:\"%s\"@]" loc id
  | id, External token, _ ->
      Format.fprintf ppf "@[<h 0>//external//\"%s\"@ <-@ %a@]" id Token.pp token
  | id, Register, _ -> Format.fprintf ppf "%s" id
  | id, Label, _ -> Format.fprintf ppf "%s" id
  | id, MemoryAddress, _ -> Format.fprintf ppf "%s" id

let pp ppf (id, _, _) = Format.fprintf ppf "%s" id

let equal ((id1, tag1, _) : t) ((id2, tag2, _) : t) =
  if String.equal id1 id2 then
    match (tag1, tag2) with
    | A _, A _ | B _, B _ | External _, External _ | Register, Register -> true
    | _ -> assert false
  else false

(** トップレベル関数やグローバル配列のラベル (caml2html: id_l) *)
type l = L of t [@@deriving show, eq]

let pp_t_list ~pp_sep ppf (ts : t list) =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.pp_print_text ppf pp_sep)
    pp ppf ts

let counter = ref 0

let genid ((id, token, dummy) : t) =
  incr counter;
  (Printf.sprintf "%s.%d" id !counter, token, dummy)

let dummy () = ()
let genid_l where : t = genid ("l", B where, dummy)
let genid_t where : t = genid ("t", B where, dummy)

let genid_prefix ~prefix ((id, where, _) : t) : t =
  assert (not (String.equal prefix ""));
  genid (prefix ^ id, where, dummy)

let genid_suffix ~suffix ((id, where, _) : t) : t =
  assert (not (String.equal suffix ""));
  genid (id ^ suffix, where, dummy)

let id_of_typ = function
  | Type.Unit -> "u"
  | Type.Bool -> "b"
  | Type.Int -> "i"
  | Type.Float -> "d"
  | Type.Fun _ -> "f"
  | Type.Tuple _ -> "t"
  | Type.Array _ -> "a"
  | Type.Var _ -> assert false

let gentmp typ where : t =
  incr counter;
  (Printf.sprintf "T%s%d" (id_of_typ typ) !counter, B where, dummy)

let make (token : Token.t) : t =
  if Token.isUnderscore token then (
    incr counter;
    (Printf.sprintf "__%%underscore%%_%d" !counter, A token, dummy))
  else (token.text, A token, dummy)

let makeRegister (name : string) : t =
  assert (String.starts_with ~prefix:"%" name || name = "min_caml_hp")
  [@ppwarning "TODO: rewrite this ugly implementation"];
  (name, Register, dummy)

let makeExternal ~name ~(origin : Token.t) : t = (name, External origin, dummy)
let isRegister ((_, k, _) : t) = k = Register
let toString ((id, _, _) : t) = id
let blackMagic ~offset ~(base_reg:t) = assert (isRegister base_reg); (Printf.sprintf "%d(%s)" offset (toString base_reg), MemoryAddress, dummy)
let compare (id1, _, _) (id2, _, _) = String.compare id1 id2
let resetCounter () = counter := 0
let je, jne = (("je", Label, dummy), ("jne", Label, dummy))
let jle, jg = (("jle", Label, dummy), ("jg", Label, dummy))
let jge, jl = (("jge", Label, dummy), ("jl", Label, dummy))
let jbe, ja = (("jbe", Label, dummy), ("ja", Label, dummy))

type cmp = JE | JNE | JLE | JG | JGE | JL | JBE | JA
let toId = function JE -> je | JNE -> jne | JLE -> jle | JG -> jg | JGE -> jge | JL -> jl | JBE -> jbe | JA -> ja
let pp_cmp ppf cmp = pp ppf (toId cmp)
let genElse cmp = genid_suffix ~suffix:"_else" (toId cmp)
let genCont cmp = genid_suffix ~suffix:"_cont" (toId cmp)
