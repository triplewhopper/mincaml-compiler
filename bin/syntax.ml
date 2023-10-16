type t = (** MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit
  | Bool of bool 
  | Int of int 
  | Float of float 
  | Not of ast
  | Neg of ast 
  | Add of ast * ast 
  | Sub of ast * ast 
  | FNeg of ast 
  | FAdd of ast * ast 
  | FSub of ast * ast 
  | FMul of ast * ast 
  | FDiv of ast * ast 
  | Eq of ast * ast 
  | Neq of ast * ast
  | LT of ast * ast
  | LE of ast * ast
  | GT of ast * ast
  | GE of ast * ast 
  | If of ast * ast * ast 
  | Let of (Id.t * Type.t) * ast * ast 
  | Var of Id.t 
  | LetRec of fundef * ast 
  | App of ast * ast list 
  | Tuple of ast list 
  | LetTuple of (Id.t * Type.t) list * ast * ast 
  | Array of ast * ast 
  | Get of ast * ast 
  | Put of ast * ast * ast [@@deriving show]
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : ast } [@@deriving show]
and ast = {
  value: t;
  tokens: Token.t NList.t [@printer fun fmt tokens -> if NList.is_empty tokens = false then Format.fprintf fmt "%a" (NList.pp Token.pp) tokens];
  prev: ast option [@printer fun fmt prev -> if Option.is_some prev then Format.fprintf fmt "%a" pp_ast (Option.get prev)];
  father: ast option [@printer fun fmt father -> if Option.is_some father then Format.fprintf fmt "<father>"];
} [@@deriving show]

(** [makeAst ~tokens value] generates an AST node with [value] and [tokens].

    [tokens] must not be empty. *)
let makeAst ~tokens value = assert (NList.is_empty tokens = false); { value; tokens; prev=None; father=None }
let makeAstWithPrev ~prev value  = { value; tokens=NList.empty; prev=Some prev; father=None }
let makeAstWithFather ~father value = { value; tokens=NList.empty; prev=None; father=Some father }
let pp_t_list ppf lst = (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_text ppf ", ") pp ppf lst)
