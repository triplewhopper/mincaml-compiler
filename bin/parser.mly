%{
(* parserが利用する変数、関数、型などの定義 *)
open Syntax
let addtyp loc x = (Id.make (Token.make loc x), Type.gentyp ())
let singleton loc text = NList.Singleton (Token.make loc text)
let prefix ~loc ~text seq = NList.Nested [singleton loc text; seq]
let suffix ~loc ~text seq = NList.Nested [seq; singleton loc text]
let binary seq1 ~loc ~text seq2 = NList.Nested [seq1; singleton loc text; seq2]
%}

/* (* 字句を表すデータ型の定義 (caml2html: parser_token) *) */
%token <bool> BOOL
%token <string> INT
%token <string> FLOAT
%token NOT "not"
%token MINUS "-"
%token PLUS "+"
%token FMINUS "-."
%token FPLUS "+."
%token FTIMES "*."
%token FDIV "/."
%token EQ "="
%token NEQ "<>"
%token LE "<="
%token GE ">="
%token LT "<"
%token GT ">"
%token IF "if"
%token THEN "then"
%token ELSE "else"
%token <string> ID
%token LET "let"
%token IN "in"
%token REC "rec"
%token COMMA ","
%token ARRAY_MAKE "Array.make" ARRAY_CREATE "Array.create" 
%token DOT "."
%token ASSIGN "<-"
%token SEMI ";"
%token LPAR "("
%token RPAR ")"
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
%type <Syntax.ast option> toplevel
%type <Syntax.ast> exp
%type <Syntax.ast> simple_exp
%type <Syntax.fundef * Token.t NList.t> fundef
%start toplevel

%%

toplevel: 
| EOF
    { None }
| exp EOF
    { Some($1) }
;

simple_exp: /* (* 括弧をつけなくても関数の引数になれる式 (caml2html: parser_simple) *) */
| LPAR exp RPAR
    { let tokens = NList.Nested [singleton $loc($1) "("; $2.tokens; singleton $loc($3) ")"] in makeAst $2.value ~tokens }
| LPAR RPAR
    { makeAst Unit ~tokens:(NList.Nested [singleton $loc($1) "("; singleton $loc($2) ")"]) }
| BOOL
    { makeAst (Bool($1)) ~tokens:(singleton $loc($1) (string_of_bool $1)) }
| INT
    { makeAst (Int(int_of_string $1)) ~tokens:(singleton $loc($1) $1) }
| FLOAT
    { makeAst (Float(float_of_string $1)) ~tokens:(singleton $loc($1) $1) }
| ID
    { makeAst (Var(Id.make (Token.make $loc($1) $1))) ~tokens:(singleton $loc($1) $1) }
| simple_exp DOT LPAR exp RPAR { 
    let tokens = NList.Nested [
        $1.tokens;
        singleton $loc($2) ".";
        singleton $loc($3) "(";
        $4.tokens;
        singleton $loc($5) ")"
    ] in
    makeAst (Get($1, $4)) ~tokens }

exp: /* (* 一般の式 (caml2html: parser_exp) *) */
| simple_exp
    { $1 }
| NOT exp
    %prec prec_app
    { makeAst (Not($2)) ~tokens:(prefix ~loc:$loc($1) ~text:"not" $2.tokens) }
| MINUS exp
    %prec prec_unary_minus
    { let v = match $2.value with
    | Float(f) -> Float(-.f)(* -1.23などは型エラーではないので別扱い *)
    | e -> Neg($2) in makeAst v ~tokens:(prefix ~loc:$loc($1) ~text:"-" $2.tokens) }
| exp PLUS exp /* (* 足し算を構文解析するルール (caml2html: parser_add) *) */
    { makeAst (Add($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"+" $3.tokens) }
| exp MINUS exp
    { makeAst (Sub($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"-" $3.tokens) }
| exp EQ exp
    { makeAst (Eq($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"=" $3.tokens) }
| exp NEQ exp
    { makeAst (Neq($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"<>" $3.tokens) 
     (* some float comparisons differ from OCaml for NaN; see: https://github.com/esumii/min-caml/issues/13#issuecomment-1147032750 *) }
| exp LT exp
    { makeAst (LT($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"<" $3.tokens) }
| exp GT exp
    { makeAst (GT($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:">" $3.tokens) }
| exp LE exp
    { makeAst (LE($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"<=" $3.tokens) }
| exp GE exp
    { makeAst (LE($3, $1)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:">=" $3.tokens) }
| IF exp THEN exp ELSE exp
    %prec prec_if
    { makeAst (If($2, $4, $6)) ~tokens:(NList.Nested [
        singleton $loc($1) "if";
        $2.tokens;
        singleton $loc($3) "then";
        $4.tokens;
        singleton $loc($5) "else";
        $6.tokens
    ]) }
| FMINUS exp
    %prec prec_unary_minus
    { makeAst (FNeg($2)) ~tokens:(prefix ~loc:$loc($1) ~text:"-" $2.tokens) }
| exp FPLUS exp
    { makeAst (FAdd($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"+." $3.tokens) }
| exp FMINUS exp
    { makeAst (FSub($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"-." $3.tokens) }
| exp FTIMES exp
    { makeAst (FMul($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"*." $3.tokens) }
| exp FDIV exp
    { makeAst (FDiv($1, $3)) ~tokens:(binary $1.tokens ~loc:$loc($2) ~text:"/." $3.tokens) }
| LET ID EQ exp IN exp
    %prec prec_let
    { makeAst (Let(addtyp $loc($2) $2, $4, $6)) ~tokens:(NList.Nested [
        singleton $loc($1) "let";
        singleton $loc($2) $2;
        singleton $loc($3) "=";
        $4.tokens;
        singleton $loc($5) "in";
        $6.tokens
    ]) }
| LET REC fundef IN exp
    %prec prec_let
    { let def, tks = $3 in makeAst (LetRec(def, $5)) ~tokens:(NList.Nested [
        singleton $loc($1) "let";
        singleton $loc($2) "rec";
        tks;
        singleton $loc($4) "in";
        $5.tokens
    ]) }
| simple_exp actual_args
    %prec prec_app
    { makeAst (App($1, $2)) ~tokens:(NList.Nested [
        $1.tokens;
        NList.Nested (List.map (fun e -> e.tokens) $2)
    ]) }
| elems
    %prec prec_tuple
    { let a, b = $1 in makeAst (Tuple(a)) ~tokens:(NList.Nested b) }
| LET LPAR pat RPAR EQ exp IN exp
    { let pat, pat_tks = $3 in makeAst (LetTuple(pat, $6, $8)) ~tokens:(NList.Nested [
        singleton $loc($1) "let";
        singleton $loc($2) "(";
        NList.Nested pat_tks;
        singleton $loc($4) ")";
        singleton $loc($5) "=";
        $6.tokens;
        singleton $loc($7) "in";
        $8.tokens
    ]) }
| simple_exp DOT LPAR exp RPAR ASSIGN exp
    { makeAst (Put($1, $4, $7)) ~tokens:(NList.Nested [
        $1.tokens;
        singleton $loc($2) ".";
        singleton $loc($3) "(";
        $4.tokens;
        singleton $loc($5) ")";
        singleton $loc($6) "<-";
        $7.tokens
    ]) }
| exp SEMI exp
    { makeAst (Let((Id.gentmp Type.Unit __LOC__, Type.Unit), $1, $3)) ~tokens:(NList.Nested [
        $1.tokens;
        singleton $loc($2) ";";
        $3.tokens
    ]) }
| array_create_or_array_make simple_exp simple_exp
    %prec prec_app
    { makeAst (Array($2, $3)) ~tokens:(NList.Nested [
        $1;
        $2.tokens;
        $3.tokens
    ]) }
// | error

%inline array_create_or_array_make:
| ARRAY_CREATE
    { singleton $loc($1) "Array.create" }
| ARRAY_MAKE
    { singleton $loc($1) "Array.make" }


fundef:
| ID formal_args EQ exp
    { let a, b = $2 in { name = addtyp $loc($1) $1; args = a; body = $4 }, NList.Nested [
        singleton $loc($1) $1;
        NList.Nested b;
        singleton $loc($3) "=";
        $4.tokens
    ] }

formal_args:
| ID formal_args
    { let a, b = $2 in (addtyp $loc($1) $1 :: a), (singleton $loc($1) $1 :: b) }
| ID
    { [addtyp $loc($1) $1], [singleton $loc($1) $1] }

actual_args:
| actual_args simple_exp
    %prec prec_app
    { $1 @ [$2] }
| simple_exp
    %prec prec_app
    { [$1] }

elems:
| elems COMMA exp
    { let a, b = $1 in (a @ [$3]), (b @ [singleton $loc($2) ","; $3.tokens])}
| exp COMMA exp
    { [$1; $3], [$1.tokens; singleton $loc($2) ","; $3.tokens] }

pat:
| pat COMMA ID { let a, b = $1 in (a @ [addtyp $loc($3) $3]), (b @ [singleton $loc($2) ","; singleton $loc($3) $3]) }

| ID COMMA ID
    { [addtyp $loc($1) $1; addtyp $loc($3) $3], [singleton $loc($1) $1; singleton $loc($2) ","; singleton $loc($3) $3] }
