{
    exception Eof
    open Parser
    let tokens = ref []
    let add t = tokens := t :: !tokens; t
}
let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ]
let ident = alpha (alpha | digit | ''')*

rule token = parse
| '\n'         {Lexing.new_line lexbuf; token lexbuf}
| (' '|'\t'|'\r') +       { token lexbuf }

| "(*"         { comment lexbuf; token lexbuf }
| "+"          { add PLUS }
(* | "*"          { TIMES } *)
| "-"          { add MINUS }
(* | "/"          { DIV } *)

| "+."         { add FPLUS }
| "*."         { add FTIMES }
| "-."         { add FMINUS }
| "/."         { add FDIV }

| "="          { add EQ }
| "<>"         { add NEQ }
| "_"          { add (ID ("__" ^ Id.gentmp Type.Unit)) }

| "<"          { add LT }
| "<="         { add LE }
| ">"          { add GT }
| ">="         { add GE }

| "<-"        { add ASSIGN }

| "let"        { add LET }
| "rec"        { add REC }
| "in"         { add IN }

| "if"         { add IF }
| "then"       { add THEN }
| "else"       { add ELSE }
| "not"        { add NOT }

| "true"       { add (BOOL (true)) }
| "false"      { add (BOOL (false)) }
| "Array.create" { add ARRAY_CREATE }
| "Array.make" { add ARRAY_MAKE }

| "."          { add DOT }
| ","          { add COMMA }
| "("          { add LPAR }
| ")"          { add RPAR }
| ";"          { add SEMI }

| digit+ as n  { add (INT n) }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)? as f { add (FLOAT f) }
| ident  as id { add (ID id) }
| eof          { add EOF }
| _ { failwith (
    "Unknown Token: " ^ Lexing.lexeme lexbuf
    ^ " at line " ^ string_of_int (Lexing.lexeme_start_p lexbuf).pos_lnum
    ^ ", character " ^ string_of_int ((Lexing.lexeme_start_p lexbuf).pos_cnum - (Lexing.lexeme_start_p lexbuf).pos_bol)) }

and comment = parse
| "*)"        { () }
| '\n'        { Lexing.new_line lexbuf; comment lexbuf }
| "(*"        { comment lexbuf; comment lexbuf }
| eof         { failwith "Comment not terminated" }
| _           { comment lexbuf }