{
    exception Eof
    open Parser
}
let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ]
let ident = alpha (alpha | digit | ''')*

rule main = parse
| '\n'         {Lexing.new_line lexbuf; main lexbuf}
| (' '|'\t'|'\r') +       { main lexbuf }

| "(*"         { comment lexbuf; main lexbuf }
| "+"          { PLUS }
| "*"          { TIMES }
| "-"          { MINUS }
| "/"          { DIV }

| "+."         { FPLUS }
| "*."         { FTIMES }
| "-."         { FMINUS }
| "/."         { FDIV }

| "="          { EQ }
| "<>"         { NEQ }
| "_"          { UNDERSCORE }

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

| "true"       { BOOL (true) }
| "false"      { BOOL (false) }
| "Array.make" { ID "Array.make" }

| "."          { DOT }
| ","          { COMMA }
| "("          { LPAR }
| ")"          { RPAR }
| ";"          { SEMI }

| digit+ as n  { INT n }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)? as f { FLOAT f }
| ident  as id { ID id }
| eof          { EOF }
| _            { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}

and comment = parse
| "*)"        { () }
| '\n'        { Lexing.new_line lexbuf; comment lexbuf }
| "(*"        { comment lexbuf; comment lexbuf }
| eof         { failwith "Comment not terminated" }
| _           { comment lexbuf }