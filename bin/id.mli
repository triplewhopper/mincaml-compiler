type t
type l = L of t
type cmp = JE | JNE | JLE | JG | JGE | JL | JBE | JA
val pp: Format.formatter -> t -> unit
val pp_id: Format.formatter -> t -> unit
val pp_l: Format.formatter -> l -> unit
val pp_t_list: pp_sep:string -> Format.formatter -> t list -> unit
val pp_cmp: Format.formatter -> cmp -> unit

val equal: t -> t -> bool (** compare only the internal string *)
val equal_l: l -> l -> bool (** compare only the internal string *)

val compare: t -> t -> int (** compare only the internal string *)

val toString: t -> string
val make: Token.t -> t
val makeRegister: string -> t
val makeExternal: name:string -> origin:Token.t -> t
val isRegister: t -> bool
val blackMagic: offset:int -> base_reg:t -> t
(* val toString: t -> string *)
val resetCounter: unit -> unit
val gentmp: Type.t -> string -> t
val genid: t -> t
val genid_l: string -> t
val genid_t: string -> t
val genid_prefix: prefix:string -> t -> t
val genid_suffix: suffix:string -> t -> t
val genElse: cmp -> t
val genCont: cmp -> t
