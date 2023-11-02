module Parser
import M 
import Ty
import Lexer
import Cyntax as Syntax
import Data.List
import Data.List1
import Data.Vect
import Data.List.Elem
import Data.Maybe
import Text.Parser
import Data.String
import Debug.Trace
import System
import System.File
import System.File.Virtual
import Control.App
import Control.App.Console
import Control.App.FileIO
import PrimIO

record State where 
  constructor MkState
  key: Nat
  tyvar: TypeVar
  underscore: Nat

initialState: State
initialState = MkState 0 (TyVar 0) 0

incr: M State ()
incr = MkM (\s => ((), {key$=(+1)} s))

newunderscore: M State String
newunderscore = MkM (\s => ("__underscore_" ++ show s.underscore, {underscore$=(+1)} s))

get: M State Nat
get = MkM (\s => (s.key, s))

newvar: M State TypeVar
newvar = MkM (\s => (s.tyvar, {tyvar:=case s.tyvar of TyVar n => TyVar (n+1)} s))

newvars: (n: Nat) -> M State (Vect n TypeVar)
newvars Z = pure []
newvars (S n) = pure (!newvar :: !(newvars n))

0 RT: Type
RT = M State Node

argM : Either String () -> M State String 
argM (Left s) = pure s
argM (Right ()) = newunderscore

argsM : Traversable t => t (Either String ()) -> M State (t String) 
argsM args = traverse id (map argM args)

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

lookahead : MinCamlTokenKind -> Grammar state MinCamlToken False MinCamlToken
lookahead k = nextIs "" (\tok => tok.kind == k) 
lookaheads : List MinCamlTokenKind -> Grammar state MinCamlToken False MinCamlToken
lookaheads ks = nextIs "" (\tok => tok.kind `elem` ks) 

[a1] Show MinCamlToken where 
    show (Tok kind text) = """
    '\{text}' as \{show kind}
    """

[a2] Show Bounds where 
    show (MkBounds ln0 cl0 ln1 cl1) = 
        if ln0 == ln1 then """
        line \{show (ln0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}
        """
        else "line \{show (ln0+1)}-\{show (cl0+1)}, characters \{show (ln1+1)}-\{show (cl1+1)}"

[a3] Show (WithBounds MinCamlToken) where
    show (MkBounded tok _ bounds) = "\{show @{a2} bounds}, \{show @{a1} tok}"

match : (k: MinCamlTokenKind) -> Grammar state MinCamlToken True (TokType k)
match k = Text.Parser.match k <|> (do tok <- bounds peek; failLoc tok.bounds "expected \{show k}, got \{show tok.val.text}")

%hide Text.Parser.match

info : (msg : String) -> (result : a) -> a
info x val = unsafePerformIO (do 
    fPutStrLn stderr ("[info] "++ x) >>= (\err => case err of 
        Left err => putStrLn $ show err
        Right () => pure ())
    pure val)

mutual
    toplevel: Grammar state MinCamlToken True RT
    toplevel = parseExpr <* match EOF
    
    parseExpr: Grammar state MinCamlToken True RT
    parseExpr = lookahead LET *> parseLet <|> parseSemi

    parseLet: Grammar state MinCamlToken True RT
    parseLet = do 
        match LET 
        lookahead REC *> parseLetRec' <|> lookahead LPAREN *> parseLetTuple' <|> parseLet'
    where 
        parseLet': Grammar state MinCamlToken True RT 
        parseLet' = do 
            name <- choose (match IDENT) (match UNDERSOCRE)
            match EQ
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            pure $ letM (argM name) e1 e2
            where 
                letM: M State String -> RT -> RT -> RT
                letM id e1 e2 = do
                    e1 <- e1; incr
                    e2 <- e2; incr
                    pure $ (Let !id !newvar e1 e2 {key=(!get)})

        parseLetTuple': Grammar state MinCamlToken True RT
        parseLetTuple' = let (>>=) = seq in do 
            match LPAREN
            name0 <- choose (match IDENT) (match UNDERSOCRE)
            name1:::names <- some (match COMMA *> choose (match IDENT) (match UNDERSOCRE)) <* match RPAREN
            match EQ
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            pure $ letTupleM (argsM (name0::name1::Vect.fromList names)) e1 e2
        where
            letTupleM: {n: Nat} -> M State (Vect (2 + n) String) -> RT -> RT -> RT
            letTupleM args e1 e2 = do
                e1 <- e1; incr
                e2 <- e2; incr
                pure $ (LetTuple !args !(newvars $ 2 + n) e1 e2 {key=(!get)})
        
        parseLetRec': Grammar state MinCamlToken True RT
        parseLetRec' = let (>>=) = seq in do 
            match REC
            name <- match IDENT
            arg0:::args <- some (choose (match IDENT) (match UNDERSOCRE))
            match EQ
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            pure $ letRecM name (argsM $ arg0::Vect.fromList args) e1 e2
        where 
            letRecM: {n: Nat} -> String -> M State (Vect (1 + n) String) -> RT -> RT -> RT
            letRecM {n} f args e1 e2 = do
            e1 <- e1; incr
            e2 <- e2; incr
            pure $ (LetRec (MkFunDef f !newvar !args !(newvars (1 + n)) e1) e2 {key=(!get), nArgs=n})

    parseSemi: Grammar state MinCamlToken True RT
    parseSemi = do 
        e <- lookahead IF *> parseIf <|> parsePut
        -- info ("parseSemi: lookahead=" ++ show @{a3} !(bounds peek)) pure ()
        lookahead SEMICOLON *> parseSemi1 e <|> pure e
    where 
        parseSemi1: RT -> Grammar state MinCamlToken True RT
        parseSemi1 e1 = do 
            match SEMICOLON; commit
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parsePut
            e2 <- lookahead SEMICOLON *> parseSemi1 e2 <|> pure e2
            pure $ semiM e1 e2
        where 
            semiM: RT -> RT -> RT
            semiM e1 e2 = do e1 <- e1; incr; e2 <- e2; incr; pure $ (Semi e1 e2 {key=(!get)})

    parseIf: Grammar state MinCamlToken True RT
    parseIf = do 
        match IF
        e1 <- parseExpr
        match THEN
        e2 <- parseExpr
        match ELSE
        e3 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parsePut
        pure $ ifM e1 e2 e3
        where 
            ifM: RT -> RT -> RT -> RT
            ifM e1 e2 e3 = do 
                e1 <- e1; incr
                e2 <- e2; incr
                e3 <- e3; incr
                pure $ (If e1 e2 e3 {key=(!get)})
    
    parsePut: Grammar state MinCamlToken True RT
    parsePut = do 
        e <- parseTuple 
        lookahead ASSIGN *> parsePut1 e <|> pure e
    where 
        parsePut1: RT -> Grammar state MinCamlToken True RT
        parsePut1 e1 = do 
            match ASSIGN
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseTuple
            e2 <- lookahead ASSIGN *> parsePut1 e2 <|> pure e2
            pure $ putM e1 e2
        where 
            putM: RT -> RT -> RT
            putM e1 e2 = do 
                e1 <- e1; incr
                e2 <- e2; incr
                pure $ (Put e1 e2 {key=(!get)})

    parseTuple: Grammar state MinCamlToken True RT
    parseTuple = do 
        e0 <- parseCmp
        lookahead COMMA *> parseTuple1 e0 <|> pure e0
    where 
        parseTuple1: RT -> Grammar state MinCamlToken True RT
        parseTuple1 e0 = let (>>=) = seq in do 
            e1:::es <- some (match COMMA *> (lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseCmp))
            pure $ tupleM (e0::e1::Vect.fromList es)
        where 
            tupleM: {n: Nat} -> Vect (2 + n) RT -> RT 
            tupleM {n} es = do 
                es <- traverse id es; Prelude.pure $ (Tuple es !(newvars (2 + n)) {key=(!get)})

    parseCmp: Grammar state MinCamlToken True RT
    parseCmp = do 
        e <- parseAddSub
        lookahead EQ *> parseCmp1 e (match EQ) eqM <|> lookahead NEQ *> parseCmp1 e (match NEQ) neqM <|>
        lookahead LT *> parseCmp1 e (match LT) ltM <|> lookahead LE *> parseCmp1 e (match LE) leM <|>
        lookahead GT *> parseCmp1 e (match GT) gtM <|> lookahead GE *> parseCmp1 e (match GE) geM <|> pure e
    where 
        parseCmp1: RT -> Grammar state MinCamlToken True () -> (RT -> RT -> RT) -> Grammar state MinCamlToken True RT
        parseCmp1 e1 match' m = do
            match'
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseAddSub
            e <- pure $ m e1 e2
            lookahead EQ *> parseCmp1 e (match EQ) eqM <|> lookahead NEQ *> parseCmp1 e (match NEQ) neqM <|>
            lookahead LT *> parseCmp1 e (match LT) ltM <|> lookahead LE *> parseCmp1 e (match LE) leM <|>
            lookahead GT *> parseCmp1 e (match GT) gtM <|> lookahead GE *> parseCmp1 e (match GE) geM <|> pure e

    parseAddSub: Grammar state MinCamlToken True RT
    parseAddSub = do 
        e <- parseMulDiv
        lookahead ADD *> parseAddSub1 e (match ADD) addM <|> lookahead MINUS *> parseAddSub1 e (match MINUS) subM <|>
        lookahead FADD *> parseAddSub1 e (match FADD) fAddM <|> lookahead FMINUS *> parseAddSub1 e (match FMINUS) fSubM <|> pure e
    where 
        parseAddSub1: RT -> Grammar state MinCamlToken True () -> (RT -> RT -> RT) -> Grammar state MinCamlToken True RT
        parseAddSub1 e1 match' m = do
            match'
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseMulDiv
            e <- pure $ m e1 e2
            lookahead ADD *> parseAddSub1 e (match ADD) addM <|> lookahead MINUS *> parseAddSub1 e (match MINUS) subM <|>
            lookahead FADD *> parseAddSub1 e (match FADD) fAddM <|> lookahead FMINUS *> parseAddSub1 e (match FMINUS) fSubM <|> pure e

    parseMulDiv: Grammar state MinCamlToken True RT
    parseMulDiv = do 
        e <- parseUnary
        lookahead FMUL *> parseFMul1 e <|>
        lookahead FDIV *> parseFDiv1 e <|> pure e
    where 
        parseFMul1: RT -> Grammar state MinCamlToken True RT
        parseFDiv1: RT -> Grammar state MinCamlToken True RT

        parseFMul1 e1 = do 
            match FMUL
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseUnary
            e <- pure $ fMulM e1 e2
            lookahead FMUL *> parseFMul1 e <|> lookahead FDIV *> parseFDiv1 e <|> pure e
        
        parseFDiv1 e1 = do 
            match FDIV
            e2 <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseUnary
            e <- pure $ fDivM e1 e2
            lookahead FMUL *> parseFMul1 e <|> lookahead FDIV *> parseFDiv1 e <|> pure e

    parseUnary: Grammar state MinCamlToken True RT
    parseUnary = do 
        lookahead MINUS *> parseNeg <|> lookahead FMINUS *> parseFNeg <|> parseApp 
    where
        parseNeg: Grammar state MinCamlToken True RT
        parseNeg = do 
            match MINUS
            e <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseUnary
            pure $ negM e
            where 
                negM: RT -> RT
                negM e = do 
                    e <- e; incr; case e of F _ => pure $ (FNeg e {key=(!get)});  _ => pure $ (Neg e {key=(!get)})

        parseFNeg: Grammar state MinCamlToken True RT
        parseFNeg = do 
            match FMINUS
            e <- lookahead LET *> parseLet <|> lookahead IF *> parseIf <|> parseUnary
            pure $ fNegM e
            where 
                fNegM: RT -> RT
                fNegM e = do 
                    e <- e; incr; pure $ (FNeg e {key=(!get)})

    parseApp: Grammar state MinCamlToken True RT
    parseApp = do 
        e <- parseGet
        parseApp1 e <|> pure e
    where 
        parseApp1: RT -> Grammar state MinCamlToken True RT
        parseApp1 e1 = do 
            args <- some parseGet
            e <- pure $ appM e1 args
            parseApp1 e <|> pure e
        where 
            appM: RT -> List1 RT -> RT
            appM f args = do 
                f <- f; arg0:::args'' <- args'; incr; 
                pure $ (App f !newvar (arg0::Vect.fromList args'') !newvar {key=(!get)})
            where 
                args' : M State (List1 Node)
                args' = traverse (\x => incr >> x) args

    parseGet: Grammar state MinCamlToken True RT
    parseGet = do 
        e <- parseAtomic
        lookahead DOT *> parseGet1 e <|> pure e
    where 
        parseGet1: RT -> Grammar state MinCamlToken True RT
        parseGet1 e1 = do 
            match DOT
            match LPAREN
            e <- parseExpr
            match RPAREN
            e <- pure $ getM e1 e
            parseGet1 e <|> pure e
        where
            getM: RT -> RT -> RT
            getM e1 e2 = do 
                e1 <- e1; incr; e2 <- e2; incr; pure $ (Get e1 e2 {key=(!get)})

    parseAtomic: Grammar state MinCamlToken True RT
    parseAtomic = do 
        lookahead INT *> parseInt <|> 
        lookahead FLOAT *> parseFloat <|>
        lookahead IDENT *> parseIdent <|>
        lookahead LPAREN *> parseParen <|>
        lookahead BOOL *> parseBool
    where 
        parseInt: Grammar state MinCamlToken True RT
        parseInt = do 
            i <- match INT
            info "parseInt matched \{i}" $ when (parseInteger i == Nothing) $ fail "illegal integer literal"
            pure $ intM (case parseInteger {a=Int} i of Just x => x; Nothing => 2147483647)
            where 
                intM: Int -> RT
                intM i = pure $ (I i {key=(!get)})

        parseFloat: Grammar state MinCamlToken True RT
        parseFloat = let (>>=) = seq in do 
            f <- match FLOAT
            let f = case parseDouble f of Just x => x; Nothing => 0.0 / 0.0
            info "parseFloat matched \{show f}" $ when (f /= f) $ fail "illegal float literal"
            pure $ floatM f
            where 
                floatM: Double -> RT
                floatM f = pure $ (F f {key=(!get)})

        parseIdent: Grammar state MinCamlToken True RT
        parseIdent = do 
            name <- match IDENT
            pure $ identM name
            where 
                identM: String -> RT
                identM name = pure $ (Var name {key=(!get)})

        parseParen: Grammar state MinCamlToken True RT
        parseParen = do 
            match LPAREN
            e <- lookahead RPAREN *> parseUnit <* match RPAREN <|> parseExpr <* match RPAREN
            pure e
            where 
                parseUnit: Grammar state MinCamlToken False RT
                parseUnit = pure $ unitM
                where 
                    unitM: RT
                    unitM = pure $ (U {key=(!get)})

        parseBool: Grammar state MinCamlToken True RT
        parseBool = do 
            b <- match BOOL
            pure $ boolM b
            where 
                boolM: Bool -> RT
                boolM b = pure $ (B b {key=(!get)})


showParsingError: String -> ParsingError MinCamlToken -> String
showParsingError file (Error msg Nothing) = "File \{show file}, <unkown location> \n\{msg}"
showParsingError file (Error msg (Just (MkBounds ln0 cl0 ln1 cl1))) =
  let line = if ln0 == ln1 then "line " ++ show (ln0 + 1) else "line \{show (ln0+1)}-\{show (ln1+1)}" in 
  let character = if cl0 == cl1 then "character \{show (cl0+1)}" else "characters \{show (cl0+1)}-\{show (cl1+1)}" in
  "File \{show file}, \{line}, \{character}\n\{msg}"

parseMinCaml : String -> List (WithBounds MinCamlToken) -> Bounds -> Either String Node
parseMinCaml path toks eof =
  case parse toplevel $ filter (not . ignored) (toks ++ [MkBounded (Tok EOF "<eof>") False eof]) of
    Right (l, []) => Right (runState initialState l)
    Right e => Left "contains tokens that were not consumed"
    Left e => Left (joinBy "\n" $ forget $ reverse $ showParsingError path <$> e)

parse : String -> Either String Node
parse x =
  case lexMinCaml x of
    (toks, ln, cl, "") => parseMinCaml "<string>" toks (MkBounds ln cl ln cl)
    (toks, ln, cl, rest) => Left "Failed to lex at \{show ln}:\{show cl}:\{show rest}"

parseString: String -> IO ()
parseString str = case parse str of 
    Right node => putStrLn $ show node
    Left err => putStrLn err

parseMinCamlFile: String -> App Init (Either Node String)
parseMinCamlFile path = assert_total handle (readFile path)
  (\str => do 
    let (tokens, ln, cl, rest) = lexMinCaml str
    if rest /= "" then pure $ Right "File \{show path}, line \{show ln}, character \{show cl}:\n unknown token"
      else do 
      case parseMinCaml path tokens (MkBounds ln cl ln cl) of 
        Right node => pure $ Left node
        Left err => pure $ Right err)
  (\err : IOError => pure $ Right $ show err)

main: IO ()
main = do 
  args <- getArgs
  case args of 
    _::path::args' => 
        if "--lex" `elem` args' then run (lexMinCamlFile path) else do
            res <- run (parseMinCamlFile path)
            case res of 
                Left node => putStrLn $ show node
                Right err => fPutStrLn stderr err >>= \_ => exitFailure
    self::_ => do 
      fPutStrLn stderr "Usage: \{self} <file>" >>= \_ =>
        exitFailure
    [] => do
      fPutStrLn stderr "Usage: ??? <file>" >>= \_ =>
        exitFailure
