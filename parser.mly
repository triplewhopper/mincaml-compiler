%{
  open Expr
%}

%token <string> INT
%token <bool>   BOOL
%token <string> FLOAT
%token <string> ID
%token EOF
%token LET IN 
%token REC
%token PLUS "+" TIMES "*" MINUS "-" DIV "/" 
%token FPLUS "+." FTIMES "*." FMINUS "-." FDIV "/."
%token COMMA "," UNDERSCORE "_" SEMI ";" ASSIGN "<-"
%token EQ "=" NEQ "<>" LT "<" LE "<=" GT ">" GE ">="
%token DOT "."
%token IF THEN ELSE
%token LPAR "(" RPAR ")"

%nonassoc PREC_COMMA PREC_SEMI

%nonassoc COMMA SEMI

%start toplevel
%type <t with_loc> toplevel
%%

toplevel: 
  | expr EOF { $1 }
;
let_expr:
  | LET; var=ID; "="; e1=expr; IN; e2=expr            {  expr_with_loc $loc (Let([string_option_with_loc $loc(var) (Some var) ],e1,e2)) }
  | LET; "("; vars=separated_nonempty_list(",", arg); ")"; "="; e1=expr; IN; e2=expr {  expr_with_loc $loc (Let(vars, e1, e2)) }
;
let_rec_expr:
  | LET; REC; f=ID; vars=nonempty_list(arg); "="; e1=expr; IN; e2=expr        { expr_with_loc $loc (LetRec(string_with_loc $loc(f) f, vars, e1, e2)) }
;
expr:
  | let_expr { $1 }
  | let_rec_expr { $1 }
  | begin_expr { $1 }
;

arg:
  | UNDERSCORE { string_option_with_loc $loc None }
  | ID { string_option_with_loc $loc (Some $1)}
;

begin_expr:
  | if_expr %prec PREC_SEMI { $1 }
  | begin_expr_impl  { expr_with_loc $loc (Begin $1) }
;

begin_expr_impl:
  | if_expr SEMI if_expr %prec PREC_SEMI { [$1; $3] }
  | if_expr SEMI let_expr %prec PREC_SEMI { [$1; $3] }
  | if_expr SEMI let_rec_expr %prec PREC_SEMI { [$1; $3] }
  // | e=expr SEMI {[e]}
  | if_expr SEMI begin_expr_impl { $1::$3 }
;

if_expr:
  | assign_expr { $1 }
  | IF; e1=expr; THEN; e2=expr; ELSE; e3=expr     { If (e1, e2, e3) |> expr_with_loc $loc}
;

assign_expr:
  | tuple_expr { $1 }
  | x=get_expr; "."; "(" y=expr ")"  ASSIGN; z=expr { Put(x, y, z) |> expr_with_loc $loc }
;
tuple_expr:
  | cmp_expr { $1 }
  | tuple_expr_impl { expr_with_loc $loc (Tuple $1) }
;

tuple_expr_impl:
  | cmp_expr "," cmp_expr %prec PREC_COMMA { [$1; $3] }
  | cmp_expr "," tuple_expr_impl { $1::$3 }
;

cmp_expr:
  | cmp_expr cmp_op arith_expr   { expr_with_loc $loc (Binary(string_with_loc $loc($2) $2, $1, $3))}
  | arith_expr                     { $1 }
;
%inline cmp_op:
  | "=" { "=" }
  | "<>" { "<>" }
  | "<" { "<" }
  | "<=" { "<=" }
  | ">" { ">" }
  | ">=" { ">=" }
;


arith_expr:
  | arith_expr arith_op factor_expr  { expr_with_loc $loc (Binary(string_with_loc $loc($2) $2, $1, $3)) }
  | factor_expr                 { $1 }
;
%inline arith_op:
  | "+" { "+" }
  | "-" { "-" }
  | "+." { "+." }
  | "-." { "-." }
;
factor_expr:
  | factor_expr factor_op unary_expr   { Binary(string_with_loc $loc($2) $2, $1, $3) |> expr_with_loc $loc }
  | unary_expr                         { $1 }
;

%inline factor_op:
  | "*" { "*" }
  | "/" { "/" }
  | "*." { "*." }
  | "/." { "/." }
;

unary_expr:
  | unary_op unary_expr { expr_with_loc $loc (Unary (string_with_loc $loc($1) $1, $2)) }
  | app_expr { $1 }
;
%inline unary_op:
  | "-" { "-" }
  | "-." { "-." }
  | "+" { "+" }
  | "+." { "+." }
;
app_expr:
  | app_expr get_expr { expr_with_loc $loc (App ($1, $2))}
  | get_expr          { $1 }

;
get_expr:
  | get_expr "." "(" expr ")" { Get($1, $4) |> expr_with_loc $loc }
  | atomic_expr { $1 }

atomic_expr:
  | INT             { Int($1) |> expr_with_loc $loc }
  | FLOAT           { Float($1) |> expr_with_loc $loc }
  | BOOL            { Bool($1) |> expr_with_loc $loc }
  | ID              { Var($1)|> expr_with_loc $loc }
  | "(" ")"         { Unit |> expr_with_loc $loc }
  | "(" expr ")"    { $2 }

;
