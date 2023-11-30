module Parser

import M 
import Ty
import Lexer
import Cyntax as Syntax
import Data.List
import Data.List1
import Data.Vect
import Text.Parser
import Debug.Trace
import Control.App
import Control.App.Console
import Control.App.FileIO
import System.File
import System.File.Virtual
import Language.Reflection
-- Grammar has 8 nonterminal symbols, among which 1 start symbols.
-- Grammar has 32 terminal symbols.
-- Grammar has 44 productions.
-- nullable(toplevel) = false
-- nullable(simple_exp) = false
-- nullable(pat) = false
-- nullable(fundef) = false
-- nullable(formal_args) = false
-- nullable(exp) = false
-- nullable(elems) = false
-- nullable(actual_args) = false
-- first(toplevel) = NOT MINUS LPAR LET INT IF ID FMINUS FLOAT EOF BOOL ARRAY_MAKE ARRAY_CREATE
-- first(simple_exp) = LPAR INT ID FLOAT BOOL
-- first(pat) = ID
-- first(fundef) = ID
-- first(formal_args) = ID
-- first(exp) = NOT MINUS LPAR LET INT IF ID FMINUS FLOAT BOOL ARRAY_MAKE ARRAY_CREATE
-- first(elems) = NOT MINUS LPAR LET INT IF ID FMINUS FLOAT BOOL ARRAY_MAKE ARRAY_CREATE
-- first(actual_args) = LPAR INT ID FLOAT BOOL
-- minimal(toplevel) = (* 1 *) EOF
-- minimal(simple_exp) = (* 1 *) BOOL
-- minimal(pat) = (* 3 *) ID COMMA ID
-- minimal(fundef) = (* 4 *) ID ID EQ BOOL
-- minimal(formal_args) = (* 1 *) ID
-- minimal(exp) = (* 1 *) BOOL
-- minimal(elems) = (* 3 *) BOOL COMMA BOOL
-- minimal(actual_args) = (* 1 *) BOOL
-- maximal(toplevel) = infinity
-- maximal(simple_exp) = infinity
-- maximal(pat) = infinity
-- maximal(fundef) = infinity
-- maximal(formal_args) = infinity
-- maximal(exp) = infinity
-- maximal(elems) = infinity
-- maximal(actual_args) = infinity
-- follow(toplevel) = #
-- follow(simple_exp) = THEN SEMI RPAR PLUS NEQ MINUS LT LPAR LE INT IN ID GT GE FTIMES FPLUS FMINUS FLOAT FDIV EQ EOF ELSE DOT COMMA BOOL
-- follow(pat) = RPAR COMMA
-- follow(fundef) = IN
-- follow(formal_args) = EQ
-- follow(exp) = THEN SEMI RPAR PLUS NEQ MINUS LT LE IN GT GE FTIMES FPLUS FMINUS FDIV EQ EOF ELSE COMMA
-- follow(elems) = THEN SEMI RPAR PLUS NEQ MINUS LT LE IN GT GE FTIMES FPLUS FMINUS FDIV EQ EOF ELSE COMMA
-- follow(actual_args) = THEN SEMI RPAR PLUS NEQ MINUS LT LPAR LE INT IN ID GT GE FTIMES FPLUS FMINUS FLOAT FDIV EQ EOF ELSE COMMA BOOL
-- The grammar is not SLR(1) -- 24 states have a conflict.



match : (k: MinCamlTokenKind) -> Grammar state MinCamlToken True (TokType k)
match k = try (Text.Parser.match k) <|> (do tok <- bounds peek; failLoc tok.bounds "expected \{show k}, got \{show tok.val.text}")

%hide Text.Parser.match

namespace Json
  export
  [a1] Show MinCamlToken where 
    show (Tok kind text) = """
    '\{text}' as \{show kind}
    """
  export
  [a2] Show Bounds where 
    show (MkBounds ln0 cl0 ln1 cl1) = 
      if ln0 == ln1 then """
      line \{show (ln0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}
      """
      else "line \{show (ln0+1)}-\{show (cl0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}"
  export
  [a3] Show (WithBounds MinCamlToken) where
    show (MkBounded tok _ bounds) = "\{show @{a2} bounds}, \{show @{a1} tok}"
  export 
  Show FC where 
    show (MkFC _ (ln0, cl0) (ln1, cl1)) = 
      if ln0 == ln1 then """
      line \{show (ln0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}
      """
      else "line \{show (ln0+1)}-\{show (cl0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}"
    show (MkVirtualFC _ (ln0, cl0) (ln1, cl1)) = 
      if ln0 == ln1 then """
      line \{show (ln0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}
      """
      else "line \{show (ln0+1)}-\{show (cl0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}"
    show EmptyFC = "<unknown location>"
log: TTImp -> a -> a
log term x = trace ", \{show $ show $ getFC term}: " x
mutual

  toplevel : Grammar state MinCamlToken True RT
  toplevel = do
    e <- exp 0
    match EOF
    pure e
  
  ifExp : Grammar state MinCamlToken True RT
  ifExp = do
    match IF
    commit
    e1 <- log `(exp) exp Z
    match THEN
    e2 <- exp Z
    match ELSE
    e3 <- exp 8
    pure $ ifM e1 e2 e3
    where ifM: RT -> RT -> RT -> RT
          ifM e1 e2 e3 = do
            e1 <- e1; incr
            e2 <- e2; incr
            e3 <- e3; incr
            pure $ (If e1 e2 e3 {key=(!get)})

  argM : Either String () -> M State String 
  argM (Left s) = pure s
  argM (Right ()) = newunderscore

  argsM : Traversable t => t (Either String ()) -> M State (t String) 
  argsM args = g (map argM args)
    where 
      g : t (M State String) -> M State (t String)
      g = traverse id

  letExp : M State String -> RT -> RT -> Grammar state MinCamlToken False RT
  letExp id e1 e2 = pure $ letM id e1 e2
    where letM: M State String -> RT -> RT -> RT
          letM id e1 e2 = do
            e1 <- e1; incr
            e2 <- e2; incr
            pure $ (Let !id !newvar e1 e2 {key=(!get)})

  letTupleExp : {n: Nat} -> M State (Vect (2 + n) String) -> RT -> RT -> Grammar state MinCamlToken False RT
  letTupleExp args e1 e2 = pure $ letTupleM args e1 e2
    where letTupleM: M State (Vect (2 + n) String) -> RT -> RT -> RT
          letTupleM args e1 e2 = do
            e1 <- e1; incr
            e2 <- e2; incr
            pure $ (LetTuple !args !(newvars $ 2 + n) e1 e2 {key=(!get)})

  letOrLetTupleExp: List1 (Either String ()) -> RT -> RT -> Grammar state MinCamlToken False RT
  letOrLetTupleExp (x:::[]) e1 e2 = letExp (argM x) e1 e2
  letOrLetTupleExp (x:::x'::xs') e1 e2 = letTupleExp (argsM (x::x'::(Vect.fromList xs'))) e1 e2

  letRecExp: String -> List1 (Either String ())  -> RT -> RT -> Grammar state MinCamlToken False RT
  letRecExp f (arg:::args') e1 e2 = Core.pure $ letRecM f (argsM (arg::fromList args')) e1 e2
    where letRecM: {n: Nat} -> String -> M State (Vect (1 + n) String) -> RT -> RT -> RT
          letRecM {n} f args e1 e2 = do
            e1 <- e1; incr
            e2 <- e2; incr
            pure $ (LetRec (MkFunDef f !newvar !args !(newvars (1 + n)) e1) e2 {key=(!get), nArgs=n})

  notExp: RT -> Grammar state MinCamlToken False RT
  notExp e = pure $ notM e
  notM: RT -> RT
  notM e = do e <- e; incr; pure $ (Not e {key=(!get)})

  arrayExp: RT -> RT -> Grammar state MinCamlToken False RT
  arrayExp e1 e2 = pure $ arrayM e1 e2
    where arrayM: RT -> RT -> RT
          arrayM e1 e2 = do
            e1 <- e1; incr
            e2 <- e2; incr
            pure $ (Array e1 e2 {key=(!get)})

  negExp: RT -> Grammar state MinCamlToken False RT
  negExp e = pure $ negM e
  negM: RT -> RT 
  negM e = do 
    e <- e; incr 
    case e of 
      F _ => pure $ (FNeg e {key=(!get)})
      _ => pure $ (Neg e {key=(!get)})

  fnegExp: RT -> Grammar state MinCamlToken False RT
  fnegExp e = pure $ fnegM e
  fnegM: RT -> RT 
  fnegM e = do e <- e; incr; pure $ (FNeg e {key=(!get)})
-- first(exp) = NOT MINUS LPAR LET INT IF ID FMINUS FLOAT BOOL ARRAY_MAKE ARRAY_CREATE
  appM: RT -> List1 RT -> RT
  appM f args = let (>>=) = bind in do f <- f; arg0:::args'' <- args'; incr; pure $ (App f !newvar (arg0::Vect.fromList args'') !newvar {key=(!get)})
  where args' : M State (List1 Node)
        args' = traverse (\x => incr >> x) args

  -- putExp: RT -> Grammar state MinCamlToken True RT
  -- putExp e = do 
  --   match DOT 
  --   match LPAREN
  --   commit
  --   e' <- exp
  --   match ASSIGN
  --   commit
  --   e'' <- exp
  --   pure $ putM e e' e''

  putM: RT -> RT -> RT
  putM e e' = let (>>=) = bind in do
    e <- e; incr
    e' <- e'; incr
    pure $ Put e e' {key=(!get)}

  exp : Nat -> Grammar state MinCamlToken True RT
  exp prec = let (>>=) = seq in do
    tok <- peek
    tokbounds <- position
    trace "{ \"func\": \"exp\", \"prec\": \{show prec}, \"tok\": \"\{show @{a3} (MkBounded tok False tokbounds)}\"" pure ()
    e <- 
    if tok.kind `elem` (the (List _) [LPAREN, INT, IDENT, FLOAT, BOOL]) then do 
        f <- log `(simple_exp) simple_exp
        try (do
          args <- (nextIs "exp: expected `(`, INT, IDENT, FLOAT, or BOOL" (\tok => tok.kind `elem`  (the (List _) [LPAREN, INT, IDENT, FLOAT, BOOL])) *> some (log `(simple_exp) simple_exp))
          pure $ appM f args) <|> pure f
      else if tok.kind == NOT then do 
        match NOT
        e <- assert_total exp $ the Nat 24
        notExp e
      else if tok.kind == MINUS then do 
        match MINUS
        e <- assert_total exp $ the Nat 22
        negExp e
      else if tok.kind == FMINUS then do 
        match FMINUS
        e <- assert_total exp $ the Nat 22 
        fnegExp e
      else if tok.kind == IF then do 
        ifExp
      else if tok.kind == LET then do
        match LET
        commit
        case (!peek).kind of 
          LPAREN => do 
            match LPAREN
            commit
            args <- sepBy1 (match COMMA) (choose (match IDENT) (match UNDERSOCRE))
            match RPAREN
            match EQ
            e1 <- assert_total exp Z
            match IN 
            e2 <- assert_total exp $ the Nat 4
            letOrLetTupleExp args e1 e2
          IDENT => do
            x <- match IDENT; trace "matching `=`" match EQ; e1 <- assert_total exp Z; trace "matching `in`" match IN; e2 <- assert_total exp $ the Nat 4
            letExp (pure x) e1 e2
          UNDERSOCRE => do 
            match UNDERSOCRE; match EQ; e1 <- assert_total exp Z; match IN; e2 <- assert_total exp $ the Nat 4
            letExp newunderscore e1 e2
          REC => do 
            match REC
            x <- match IDENT
            args <- someTill (match EQ) (choose (match IDENT) (match UNDERSOCRE))
            e1 <- assert_total $ log `(exp) exp Z
            match IN
            e2 <- assert_total $ log `(exp) exp $ the Nat 4
            letRecExp x args e1 e2
          _ => do 
            failLoc (!(bounds peek)).bounds "expected identifier"

      else if tok.kind == ARRAY_CREATE then do 
        match ARRAY_CREATE
        e1 <- log `(simple_exp) simple_exp
        e2 <- log `(simple_exp) simple_exp
        arrayExp e1 e2
      else do
        pos <- position
        failLoc pos "expected expression"
    trace #", "info": "parsed exp, lookahead: \#{show @{a3} (!(bounds peek))}"}"# pure ()
    e' <- nextIs "exp: try reduce" (\tok => tok.kind `elem` the (List _) [RPAREN, THEN, ELSE, IN, EOF]) *> pure e <|> nextIs "" (\tok => precOp tok.kind < prec) *> pure e <|> assert_total log `(exp1) exp1 prec e <|> pure e
    -- nextIs "exp: try FMUL" (\tok => tok.kind == FMUL && prec <= 18) *> assert_total fmul1 e <|>
    -- nextIs "" (\tok => tok.kind == FDIV && prec <= 18) *> assert_total fdiv1 e <|>
    -- nextIs "" (\tok => tok.kind == FADD && prec <= 16) *> assert_total fadd1 e <|>
    -- nextIs "" (\tok => tok.kind == FMINUS && prec <= 16) *> assert_total fminus1 e <|>
    -- nextIs "" (\tok => tok.kind == ADD && prec <= 16) *> assert_total add1 e <|>
    -- nextIs "" (\tok => tok.kind == MINUS && prec <= 16) *> assert_total minus1 e <|>
    -- nextIs "" (\tok => tok.kind == EQ && prec <= 14) *> assert_total eq1 e <|>
    -- nextIs "" (\tok => tok.kind == NEQ && prec <= 14) *> assert_total neq1 e <|>
    -- nextIs "" (\tok => tok.kind == LT && prec <= 14) *> assert_total lt1 e <|>
    -- nextIs "" (\tok => tok.kind == LE && prec <= 14) *> assert_total le1 e <|>
    -- nextIs "" (\tok => tok.kind == GT && prec <= 14) *> assert_total gt1 e <|>
    -- nextIs "" (\tok => tok.kind == GE && prec <= 14) *> assert_total ge1 e <|>
    -- nextIs "" (\tok => tok.kind == COMMA && prec <= 12) *> assert_total comma1 e <|>
    -- nextIs "" (\tok => tok.kind == ASSIGN && prec <= 11) *> assert_total assign1 e <|>
    -- nextIs "" (\tok => trace "testing semicolon! at prec \{show prec}" tok.kind == SEMICOLON && prec <= 7) *> assert_total semicolon1 e <|> pure e
    trace """
    , "info": ["exp", \{show prec}, "\{show @{a2} tokbounds}", "\{show @{a2} (!(bounds peek)).bounds}"] }
    """ pure e'

  exp1: Nat -> RT -> Grammar state MinCamlToken True RT
  exp1 prec e = let (>>=) = seq in do 
    let prec' = precOp (!peek).kind
    trace #"{ "func": "exp1", "prec": \#{show prec}, "prec' ": \#{show prec'}, "lookahead": "\#{show @{a3} (!(bounds peek))}""# pure ()
    e <- nextIs "" (\_ => prec < prec') *> log `(exp1) exp1 (S prec) e <|> pure e
    e <- nextIs "" (\_ => prec == 18) *> muldiv1 e <|> nextIs "" (\_ => prec == 16) *> addsub1 e <|> nextIs "" (\_ => prec == 14) *> cmp1 e <|> 
      nextIs "" (\_ => prec == 12) *> comma1 e <|> nextIs "" (\_ => prec == 10) *> assign1 e <|> nextIs "" (\_ => prec == 6) *> semicolon1 e
    trace #", "info": "exp1, lookahead: \#{show @{a3} (!(bounds peek))}" ] }"# pure ()
    pure e

  fmul1: RT -> Grammar state MinCamlToken True RT
  fdiv1: RT -> Grammar state MinCamlToken True RT

  precOp: MinCamlTokenKind -> Nat
  precOp FMUL = 18
  precOp FDIV = 18
  precOp FADD = 16
  precOp FMINUS = 16
  precOp ADD = 16
  precOp MINUS = 16
  precOp EQ = 14
  precOp NEQ = 14
  precOp LT = 14
  precOp LE = 14
  precOp GT = 14
  precOp GE = 14
  precOp COMMA = 12
  precOp ASSIGN = 10
  precOp SEMICOLON = 6
  precOp _ = 0


  fadd1: RT -> Grammar state MinCamlToken True RT
  fminus1: RT -> Grammar state MinCamlToken True RT
  add1: RT -> Grammar state MinCamlToken True RT
  minus1: RT -> Grammar state MinCamlToken True RT
  addsub1: RT -> Grammar state MinCamlToken True RT

  eq1: RT -> Grammar state MinCamlToken True RT
  neq1: RT -> Grammar state MinCamlToken True RT
  lt1: RT -> Grammar state MinCamlToken True RT
  le1: RT -> Grammar state MinCamlToken True RT
  gt1: RT -> Grammar state MinCamlToken True RT
  ge1: RT -> Grammar state MinCamlToken True RT
  cmp1: RT -> Grammar state MinCamlToken True RT
  
  comma1: RT -> Grammar state MinCamlToken True RT
  assign1: RT -> Grammar state MinCamlToken True RT
  semicolon1: RT -> Grammar state MinCamlToken True RT

  fmul1 e = do match FMUL; (Core.pure $ fMulM e !(assert_total exp $ the Nat 18))
  fdiv1 e = do match FDIV; (Core.pure $ fDivM e !(assert_total exp $ the Nat 18))
  muldiv1: RT -> Grammar state MinCamlToken True RT
  muldiv1 e = do e <- assert_total fmul1 e <|> assert_total fdiv1 e; try (assert_total muldiv1 e) <|> Core.pure e

  fadd1 e = do match FADD; Core.pure $ fAddM e !(assert_total exp $ the Nat 16)
  fminus1 e = do match FMINUS; Core.pure $ fSubM e !(assert_total exp $ the Nat 16)
  add1 e = do match ADD; Core.pure $ addM e !(assert_total exp $ the Nat 16)
  minus1 e = do match MINUS; Core.pure $ subM e !(assert_total exp $ the Nat 16)
  addsub1 e = do 
    e <- add1 e <|> minus1 e <|> fadd1 e <|> fminus1 e 
    assert_total nextIs "" (\tok => tok.kind `elem` (the (List _) [ADD, MINUS, FADD, FMINUS])) *> addsub1 e <|> Core.pure e
-- nextIs "" (\tok => tok.kind == FMUL || tok.kind == FDIV) *> 
  eq1 e = do match EQ; (Core.pure $ eqM e !(assert_total exp $ the Nat 14))
  neq1 e = do match NEQ; Core.pure $ neqM e !(assert_total exp $ the Nat 14)
  lt1 e = do match LT; Core.pure $ ltM e !(assert_total exp $ the Nat 14)
  le1 e = do match LE; Core.pure $ leM e !(assert_total exp $ the Nat 14)
  gt1 e = do match GT; Core.pure $ gtM e !(assert_total exp $ the Nat 14)
  ge1 e = do match GE; Core.pure $ geM e !(assert_total exp $ the Nat 14)
  cmp1 e = do 
    trace #"{ "func": "cmp1", "lookahead: \#{show @{a3} !(bounds peek)}""# Core.pure ()
    e <- eq1 e <|> neq1 e <|> lt1 e <|> le1 e <|> gt1 e <|> ge1 e
    trace #", "info": [ "cmp1, after", "lookahead: \#{show @{a3} !(bounds peek)}" ]"# Core.pure ()
    e <-  nextIs "" (\tok => tok.kind `elem` (the (List _) [EQ, NEQ, LT, LE, GT, GE])) *> cmp1 e <|> Core.pure e
    trace "} // cmp1" Core.pure e

  comma1 e = let (>>=) = seq in do Core.pure $ commaM e !(some (match COMMA >> assert_total exp (the Nat 12)))
  assign1 e = do trace #"{ "func": "assign1""# match ASSIGN; e' <- assert_total exp $ the Nat 11; e' <- assert_total nextIs "" (\tok => tok.kind == ASSIGN) *> assign1 e' <|> Core.pure e'; trace "} // assign1" $ Core.pure $ putM e e'
  semicolon1 e = do trace #"{ "func": "semicolon1""# pure ();  match SEMICOLON; e' <- assert_total exp $ the Nat 6; e' <- assert_total nextIs "" (\tok => tok.kind == SEMICOLON) *> semicolon1 e' <|> Core.pure e'; trace "} //semicolon1" $ Core.pure $ semiM e e' 

  commaM: RT -> List1 RT -> RT
  commaM e es = let (>>=) = bind in do
    e <- e; 
    e0:::es <- traverse (\x => incr >> x) es; incr
    pure $ (Tuple (e::e0::Vect.fromList es) !(newvars (2 + length es)){key=(!get)})
  binaryOps: List1 MinCamlTokenKind
  binaryOps = FMUL:::[FDIV, FMINUS, ADD, MINUS, FADD, EQ, NEQ, LT, LE, GT, GE, SEMICOLON, COMMA]


  binaryM: (Node -> Node -> Node) -> RT -> RT -> RT
  binaryM k e1 e2 = do e1 <- e1; incr; e2 <- e2; incr; pure $ k e1 e2
  
  fMulM: RT -> RT -> RT
  fDivM: RT -> RT -> RT
  fAddM: RT -> RT -> RT
  fSubM: RT -> RT -> RT
  addM: RT -> RT -> RT
  subM: RT -> RT -> RT

  eqM: RT -> RT -> RT
  neqM: RT -> RT -> RT
  ltM: RT -> RT -> RT
  leM: RT -> RT -> RT
  gtM: RT -> RT -> RT
  geM: RT -> RT -> RT

  semiM: RT -> RT -> RT

  fMulM e1 e2 = binaryM (FMul {key=(!get)}) e1 e2
  fDivM e1 e2 = binaryM (FDiv {key=(!get)}) e1 e2
  fAddM e1 e2 = binaryM (FAdd {key=(!get)}) e1 e2
  fSubM e1 e2 = binaryM (FSub {key=(!get)}) e1 e2
  addM e1 e2 = binaryM (Add {key=(!get)}) e1 e2
  subM e1 e2 = binaryM (Sub {key=(!get)}) e1 e2
  eqM e1 e2 = binaryM (Eq {key=(!get)}) e1 e2
  neqM e1 e2 = binaryM (Neq {key=(!get)}) e1 e2
  ltM e1 e2 = binaryM (Lt {key=(!get)}) e1 e2
  leM e1 e2 = binaryM (Le {key=(!get)}) e1 e2
  gtM e1 e2 = binaryM (Gt {key=(!get)}) e1 e2
  geM e1 e2 = binaryM (Ge {key=(!get)}) e1 e2
  semiM e1 e2 = binaryM (Semi {key=(!get)}) e1 e2


    

  boolLiteral : Grammar state MinCamlToken True RT
  boolLiteral = do 
    b <- match BOOL 
    pure $ do pure $ B b {key= !get}

  intLiteral : Grammar state MinCamlToken True RT
  intLiteral = let (>>=) = seq in do 
    i <- bounds $ match INT
    case filter inrange $ parseInteger i.val of 
      Just i' => Core.pure $ intM i'
      Nothing => do
        failLoc i.bounds "invalid integer literal: \{i.val}"
    where 
      inrange: Integer -> Bool
      inrange x = -2147483648 <= x && x <= 2147483647
      intM: Integer -> RT
      intM i = pure (I (cast i) {key= !get})

  floatLiteral : Grammar state MinCamlToken True RT
  floatLiteral = do 
    (bounds $ match FLOAT) `seq` \f =>
      case filter (\x => not (isnan x || isinf x)) (parseDouble f.val) of 
        Just val => pure (do pure (F val {key= !get}))
        _ => failLoc f.bounds "invalid float literal: \{f.val}"
      where 
        isnan: Double -> Bool
        isnan x = x /= x
        isinf: Double -> Bool
        isinf x = x == 1/0 || x == -1/0

  getExp : RT -> Grammar state MinCamlToken True RT
  getExp e = let (>>=) = seq in do 
    match DOT
    trace "in getExp, matching `(` at \{show (!(bounds peek)).bounds}" match LPAREN
    e' <- exp 0
    trace "in getExp, matching `)` at \{show (!(bounds peek)).bounds}" match RPAREN
    try (nextIs "getExp: expected `.`" (\tok => tok.kind == DOT) *> assert_total getExp (getM e e')) <|> pure (getM e e')
    where getM: RT -> RT -> RT
          getM e e' = do e <- e; incr; e' <- e'; incr; pure $ Get e e' {key= !get}

  ident: Grammar state MinCamlToken True RT
  ident = do 
    id <- match IDENT
    pure (do pure(Var id {key=(!get)}))

  simple_exp : Grammar state MinCamlToken True RT
  simple_exp = do
    lookahead <- bounds peek
    trace #"{ "func": "simple_exp", "lookahead": "\#{show @{a3} lookahead}""# pure ()
    e <- 
    case lookahead.val.kind of 
      BOOL => boolLiteral
      INT => intLiteral
      FLOAT => floatLiteral
      IDENT => ident
      LPAREN => do 
        match LPAREN
        case (!peek).kind of 
          RPAREN => do 
            match RPAREN
            pure (do pure (U {key= !get}))
          _ => do
            e <- exp 0
            match RPAREN
            pure e
      _ => do
        trace "} // error simple_exp" $ failLoc lookahead.bounds "simple_exp: expected expression"
    e <- try (getExp e) <|> pure e
    trace "} // simple_exp" pure e

showParsingError: String -> ParsingError MinCamlToken -> String
showParsingError file (Error msg Nothing) = "File \{show file}, <unkown location> \n\{msg}"
showParsingError file (Error msg (Just (MkBounds ln0 cl0 ln1 cl1))) =
  let line = if ln0 == ln1 then "line " ++ show (ln0 + 1) else "line \{show (ln0+1)}-\{show (ln1+1)}" in 
  let character = if cl0 == cl1 then "character \{show (cl0+1)}" else "characters \{show (cl0+1)}-\{show (cl1+1)}" in
  "File \{show file}, \{line}, \{character}\n\{msg}"

parseMinCaml : String -> List (WithBounds MinCamlToken) -> Either String Node
parseMinCaml path toks =
  case parse toplevel $ filter (not . ignored) toks of
    Right (l, []) => Right (runState l)
    Right e => Left "contains tokens that were not consumed"
    Left e => Left (joinBy "\n" $ forget $ showParsingError path <$> e)

parse : String -> Either String Node
parse x =
  case lexMinCaml x of
    (toks, ln, cl, "") => parseMinCaml "<string>" (toks ++ [MkBounded (Tok EOF "") False (MkBounds ln cl ln cl)])
    (toks, _, _, _) => Left "Failed to lex."

parseMinCamlFile: String -> App Init ()
parseMinCamlFile path = assert_total handle (readFile path)
  (\str => do 
    let (tokens, ln, cl, rest) = lexMinCaml str
    if rest /= "" then do 
      putStrLn $ "File \{show path}, line \{show ln}, character \{show cl}:\n unknown token"
      else do 
      case parseMinCaml path tokens of 
        Right node => putStrLn $ show node
        Left err => putStrLn err)
  (\err : IOError => putStrLn (show err))

main: IO ()
main = do 
  args <- getArgs
  case args of 
    _::path::args' => if "--lex" `elem` args' then run (lexMinCamlFile path) else run (parseMinCamlFile path)
    self::_ => do 
      fPutStrLn stderr "Usage: \{self} <file>" >>= \_ =>
        exitFailure
    [] => do
      fPutStrLn stderr "Usage: ??? <file>" >>= \_ =>
        exitFailure
