{
    exception Eof
    exception UnknownToken of Lexing.position * string
    exception UnTerminatedComment of Lexing.position
    exception UnTerminatedString of Lexing.position
    open Pre
}
let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ]
let ident = alpha (alpha | digit | ''')*
let lower_ident = ['a'-'z' '_'] (alpha | digit | ''')*
let backslash = '\\'
let str_lit = '"' ('\\' _ | [^ '"' '\\'])* '"'

rule token = parse
| '\n'         { Lexing.new_line lexbuf; token lexbuf }
| (' '|'\t'|'\r') + { token lexbuf }

| "(*"         { comment lexbuf; token lexbuf }
| str_lit     {
    let s = Lexing.lexeme lexbuf in
    let start = Lexing.lexeme_start lexbuf in 
    Lit (S, start, Scanf.unescaped (String.sub s 1 (String.length s - 2))) }
| "+" | "-" | "+." | "-." | "*." | "/." 
| '=' | "<>" | '<' | '>' | "<=" | ">=" | '(' | ')' 
| "<-" | '.' | ',' |  ';'  as op         { Lit (Op, Lexing.lexeme_start lexbuf, op) }

| ("true" | "false") as b       { Lit (B, Lexing.lexeme_start lexbuf, b) }
| "Array" as s { Word (Lexing.lexeme_start lexbuf, s) }

| digit+ as n  { Lit (I, Lexing.lexeme_start lexbuf, n) }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)? as f { Lit (F , Lexing.lexeme_start lexbuf, f) }
| lower_ident  as id { Word (Lexing.lexeme_start lexbuf, id) }
| eof          { Eof (Lexing.lexeme_start lexbuf) }
| _ { raise (UnknownToken (Lexing.lexeme_start_p lexbuf, Lexing.lexeme lexbuf)) }

and comment = parse
| "*)"        { () }
| '\n'        { Lexing.new_line lexbuf; comment lexbuf }
| "(*"        { comment lexbuf; comment lexbuf }
| eof         { raise (UnTerminatedComment (Lexing.lexeme_start_p lexbuf)) }
| _           { comment lexbuf }

