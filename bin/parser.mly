%{
(* parserが利用する変数、関数、型などの定義 *)
open Syntax
let addtyp x = (x, Type.gentyp ())
%}

/* (* 字句を表すデータ型の定義 (caml2html: parser_token) *) */
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token NOT
%token MINUS
%token PLUS
%token FMINUS
%token FPLUS
%token FTIMES
%token FDIV
%token EQ
%token NEQ
%token LE
%token GE
%token LT
%token GT
%token IF
%token THEN
%token ELSE
%token <Id.t> ID
%token LET
%token IN
%token REC
%token COMMA
%token ARRAY_CREATE
%token DOT
%token ASSIGN
%token SEMI
%token LPAR
%token RPAR
%token EOF

/* (* 優先順位とassociativityの定義（低い方から高い方へ） (caml2html: parser_prior) *) */
%nonassoc IN
%right prec_let
%right SEMI
%right prec_if
%right ASSIGN
%nonassoc prec_tuple
%left COMMA
%left EQ NEQ LT GT LE GE
%left PLUS MINUS FPLUS FMINUS
%left FTIMES FDIV
%right prec_unary_minus
%left prec_app
%left DOT

/* (* 開始記号の定義 *) */
%type <Syntax.t> exp
%start exp

%%

simple_exp: /* (* 括弧をつけなくても関数の引数になれる式 (caml2html: parser_simple) *) */
| LPAR exp RPAR
    { $2 }
| LPAR RPAR
    { Unit }
| BOOL
    { Bool($1) }
| INT
    { Int($1) }
| FLOAT
    { Float($1) }
| ID
    { Var($1) }
| simple_exp DOT LPAR exp RPAR
    { Get($1, $4) }

exp: /* (* 一般の式 (caml2html: parser_exp) *) */
| simple_exp
    { $1 }
| NOT exp
    %prec prec_app
    { Not($2) }
| MINUS exp
    %prec prec_unary_minus
    { match $2 with
    | Float(f) -> Float(-.f) (* -1.23などは型エラーではないので別扱い *)
    | e -> Neg(e) }
| exp PLUS exp /* (* 足し算を構文解析するルール (caml2html: parser_add) *) */
    { Add($1, $3) }
| exp MINUS exp
    { Sub($1, $3) }
| exp EQ exp
    { Eq($1, $3) }
| exp NEQ exp
    { Not(Eq($1, $3)) (* some float comparisons differ from OCaml for NaN; see: https://github.com/esumii/min-caml/issues/13#issuecomment-1147032750 *) }
| exp LT exp
    { Not(LE($3, $1)) }
| exp GT exp
    { Not(LE($1, $3)) }
| exp LE exp
    { LE($1, $3) }
| exp GE exp
    { LE($3, $1) }
| IF exp THEN exp ELSE exp
    %prec prec_if
    { If($2, $4, $6) }
| FMINUS exp
    %prec prec_unary_minus
    { FNeg($2) }
| exp FPLUS exp
    { FAdd($1, $3) }
| exp FMINUS exp
    { FSub($1, $3) }
| exp FTIMES exp
    { FMul($1, $3) }
| exp FDIV exp
    { FDiv($1, $3) }
| LET ID EQ exp IN exp
    %prec prec_let
    { Let(addtyp $2, $4, $6) }
| LET REC fundef IN exp
    %prec prec_let
    { LetRec($3, $5) }
| simple_exp actual_args
    %prec prec_app
    { App($1, $2) }
| elems
    %prec prec_tuple
    { Tuple($1) }
| LET LPAR pat RPAR EQ exp IN exp
    { LetTuple($3, $6, $8) }
| simple_exp DOT LPAR exp RPAR ASSIGN exp
    { Put($1, $4, $7) }
| exp SEMI exp
    { Let((Id.gentmp Type.Unit, Type.Unit), $1, $3) }
| ARRAY_CREATE simple_exp simple_exp
    %prec prec_app
    { Array($2, $3) }
| error
    { failwith
        (Printf.sprintf "parse error near characters %d-%d"
           (Parsing.symbol_start ())
           (Parsing.symbol_end ())) }

fundef:
| ID formal_args EQ exp
    { { name = addtyp $1; args = $2; body = $4 } }

formal_args:
| ID formal_args
    { addtyp $1 :: $2 }
| ID
    { [addtyp $1] }

actual_args:
| actual_args simple_exp
    %prec prec_app
    { $1 @ [$2] }
| simple_exp
    %prec prec_app
    { [$1] }

elems:
| elems COMMA exp
    { $1 @ [$3] }
| exp COMMA exp
    { [$1; $3] }

pat:
| pat COMMA ID
    { $1 @ [addtyp $3] }
| ID COMMA ID
    { [addtyp $1; addtyp $3] }
