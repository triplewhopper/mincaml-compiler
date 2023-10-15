{
    exception Eof
    open Parser
}
let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ]
let ident = alpha (alpha | digit | ''')*

rule token = parse
| '\n'         {Lexing.new_line lexbuf; token lexbuf}
| (' '|'\t'|'\r') +       { token lexbuf }

| "(*"         { comment lexbuf; token lexbuf }
| "+"          { PLUS }
(* | "*"          { TIMES } *)
| "-"          { MINUS }
(* | "/"          { DIV } *)

| "+."         { FPLUS }
| "*."         { FTIMES }
| "-."         { FMINUS }
| "/."         { FDIV }

| "="          { EQ }
| "<>"         { NEQ }
| "_"          { ID ("__" ^ Id.gentmp Type.Unit) }

| "<"          { LT }
| "<="         { LE }
| ">"          { GT }
| ">="         { GE }

| "<-"        { ASSIGN }

| "let"        { LET }
| "rec"        { REC }
| "in"         { IN }

| "if"         { IF }
| "then"       { THEN }
| "else"       { ELSE }
| "not"        { NOT }

| "true"       { BOOL (true) }
| "false"      { BOOL (false) }
| "Array.make" | "Array.create" { ARRAY_CREATE }

| "."          { DOT }
| ","          { COMMA }
| "("          { LPAR }
| ")"          { RPAR }
| ";"          { SEMI }

| digit+ as n  { INT (int_of_string n) }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)? as f { FLOAT (float_of_string f) }
| ident  as id { ID id }
| eof          { EOF }
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