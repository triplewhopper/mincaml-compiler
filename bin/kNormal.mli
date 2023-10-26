type ('a, 'b) link = PrevLeft of 'a | PrevRight of 'b | Father of 'a Promise.t 
type t = {
  value: exp;
  (* ssn: int; *)
  tokens: Token.t NList.t;
  prev: (t, Syntax.ast) link; 
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
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtFunApp of Id.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

val fv : t -> S.t
val f : Syntax.ast -> t

val pp: Format.formatter -> t -> unit
val pp_kn: Format.formatter -> t -> unit
val equal: t -> t -> bool
val equal_exp: exp -> exp -> bool
val shallowEq: t -> t -> bool
