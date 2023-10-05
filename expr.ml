type position = int * int
type loc = Loc of position * position

let loc ((l, r) : Lexing.position * Lexing.position) : loc =
  Loc
    ( ((*file = l.pos_fname; *) l.pos_lnum, l.pos_cnum - l.pos_bol),
      ((*file = r.pos_fname; *) r.pos_lnum, r.pos_cnum - r.pos_bol) )

type _ with_loc =
  (* 'a * string *)
  | ExprLoc : t * loc -> t with_loc
  | StringLoc : string * loc -> string with_loc
  | StringOptionLoc : string option * loc -> string option with_loc

and t =
  | Unit
  | Bool of bool
  | Int of string
  | Float of string
  | Var of string
  | Unary of string with_loc * t with_loc
  | Binary of string with_loc * t with_loc * t with_loc
  | If of t with_loc * t with_loc * t with_loc
  | Begin of t with_loc list
  | Let of string option with_loc list * t with_loc * t with_loc
  | LetRec of
      string with_loc * string option with_loc list * t with_loc * t with_loc
  | App of t with_loc * t with_loc
  | Tuple of t with_loc list
  | Array of t with_loc * t with_loc
  | Get of t with_loc * t with_loc
  | Put of t with_loc * t with_loc * t with_loc

let loc_to_json : Buffer.t -> loc -> unit =
 fun bc (Loc ((l0, r0), (l1, r1))) ->
  Printf.bprintf bc
    {|{"start":{"line":%i,"character":%i},"end":{"line":%i,"character":%i}}|} l0 r0 l1 r1

let rec list_to_json : type a. bool -> Buffer.t -> a with_loc list -> unit =
 fun loc_flag bc xs ->
  Printf.bprintf bc "[";
  List.iter
    (fun x ->
      to_json loc_flag bc x;
      Printf.bprintf bc ",")
    xs;
  Buffer.truncate bc (Buffer.length bc - 1);
  Printf.bprintf bc "]"

and expr_to_json loc_flag bc typename entires loc =
  Printf.bprintf bc "{";
  Printf.bprintf bc {|"__typename":"%s"|} typename;
  List.iter
    (fun (name, action) ->
      Printf.bprintf bc {|,"%s":|} name;
      action ())
    entires;
  if loc_flag then (
    Printf.bprintf bc {|,"loc":|};
    loc_to_json bc loc);
  Printf.bprintf bc "}"

and to_json : type a. bool -> Buffer.t -> a with_loc -> unit =
 fun loc_flag bc e ->
  match e with
  | StringLoc (s, loc) | StringOptionLoc (Some s, loc) ->
      if loc_flag then (
        Printf.bprintf bc {|{"__typename":"token","value":"%s","loc":|} s;
        loc_to_json bc loc;
        Printf.bprintf bc "}")
      else Printf.bprintf bc {|"%s"|} (String.escaped s)
  | StringOptionLoc (None, loc) ->
      if loc_flag then (
        Printf.bprintf bc {|{"__typename":"token","value":null,"loc":|};
        loc_to_json bc loc;
        Printf.bprintf bc "}")
      else Printf.bprintf bc "null"
  | ExprLoc (Unit, loc) ->
      expr_to_json loc_flag bc "unit"
        [ ("value", fun () -> Buffer.add_string bc "null") ]
        loc
  | ExprLoc (Bool b, loc) ->
      expr_to_json loc_flag bc "bool"
        [ ("value", fun () -> Printf.bprintf bc "%b" b) ]
        loc
  | ExprLoc (Int i, loc) ->
      expr_to_json loc_flag bc "int"
        [ ("value", fun () -> Printf.bprintf bc "%s" i) ]
        loc
  | ExprLoc (Float f, loc) ->
      expr_to_json loc_flag bc "float"
        [ ("value", fun () -> Printf.bprintf bc "\"%s\"" f) ]
        loc
  | ExprLoc (Var v, loc) ->
      expr_to_json loc_flag bc "var"
        [ ("name", fun () -> Printf.bprintf bc "\"%s\"" v) ]
        loc
  | ExprLoc (Unary (op, e), loc) ->
      expr_to_json loc_flag bc "unary"
        [
          ("op", fun () -> to_json loc_flag bc op);
          ("e", fun () -> to_json loc_flag bc e);
        ]
        loc
      (* Printf.bprintf bc {|{"__typename":"unary","op":|};
         to_json loc_flag bc op;
         Printf.bprintf bc {|,"e":|};
         to_json loc_flag bc e;
         Printf.bprintf bc {|}|} *)
  | ExprLoc (Binary (op, e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"binary","op":|};
         to_json loc_flag bc op;
         Printf.bprintf bc {|,"e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc {|}|} *)
      expr_to_json loc_flag bc "binary"
        [
          ("op", fun () -> to_json loc_flag bc op);
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (If (e1, e2, e3), loc) ->
      (* Printf.bprintf bc {|{"__typename":"if","e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc {|,"e3":|};
         to_json loc_flag bc e3;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "if"
        [
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
          ("e3", fun () -> to_json loc_flag bc e3);
        ]
        loc
  | ExprLoc (Begin es, loc) ->
      (* Printf.bprintf bc {|{"__typename":"begin","es":|};
         list_to_json loc_flag bc es;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "begin"
        [ ("es", fun () -> list_to_json loc_flag bc es) ]
        loc
  | ExprLoc (Let (xs, e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"let","names":|};
         list_to_json loc_flag bc xs;
         Printf.bprintf bc {|,"e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc {|}|} *)
      expr_to_json loc_flag bc "let"
        [
          ("names", fun () -> list_to_json loc_flag bc xs);
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (LetRec (name, args, e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"letrec","name":|};
         to_json loc_flag bc name;
         Printf.bprintf bc {|,"args":|};
         list_to_json loc_flag bc args;
         Printf.bprintf bc {|,"e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "letrec"
        [
          ("name", fun () -> to_json loc_flag bc name);
          ("args", fun () -> list_to_json loc_flag bc args);
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (App (e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"app","e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "app"
        [
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (Tuple es, loc) ->
      (* Printf.bprintf bc {|{"__typename":"tuple","es":|};
         list_to_json loc_flag bc es;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "tuple"
        [ ("es", fun () -> list_to_json loc_flag bc es) ]
        loc
  | ExprLoc (Array (e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"array","e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "array"
        [
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (Get (e1, e2), loc) ->
      (* Printf.bprintf bc {|{"__typename":"get","e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "get"
        [
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
        ]
        loc
  | ExprLoc (Put (e1, e2, e3), loc) ->
      (* Printf.bprintf bc {|{"__typename":"put","e1":|};
         to_json loc_flag bc e1;
         Printf.bprintf bc {|,"e2":|};
         to_json loc_flag bc e2;
         Printf.bprintf bc {|,"e3":|};
         to_json loc_flag bc e3;
         Printf.bprintf bc "}" *)
      expr_to_json loc_flag bc "put"
        [
          ("e1", fun () -> to_json loc_flag bc e1);
          ("e2", fun () -> to_json loc_flag bc e2);
          ("e3", fun () -> to_json loc_flag bc e3);
        ]
        loc

(* let rec to_yojson = function
   | Unit, loc -> `Assoc [ (("__typename", `String "unit"), ("value", `Null)) , ("loc", loc) ]
   | Bool b, loc ->
       `Assoc [ (("__typename", `String "bool"), ("value", `Bool b)) ]
   | Int i, loc -> `Assoc [ (("__typename", `String "int"), ("value", `Int i)) ]
   | Float f, loc ->
       `Assoc [ (("__typename", `String "float"), ("value", `Float f)) ]
   | Var v, loc ->
       `Assoc [ (("__typename", `String "var"), ("value", `String v)) ]
   | Unary (op, e), loc ->
       `Assoc
         [
           ( ("__typename", `String "unary"),
             ("value", `Assoc [ ("op", `String op); ("e", to_yojson e) ]) );
         ] *)

let expr_with_loc l e : t with_loc = ExprLoc (e, loc l)
let string_with_loc l s : string with_loc = StringLoc (s, loc l)

let string_option_with_loc l s : string option with_loc =
  StringOptionLoc (s, loc l)
