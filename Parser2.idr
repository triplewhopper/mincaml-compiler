module Parser2
import Ty
import NonNullString
import Info
import Lexer
import Text.Lexer
import Syntax
import Utils
import Data.List
import Data.List1
import Data.Vect
import Data.String
import Debug.Trace
import Syntax.WithProof
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Either

-- incr: StateT Nat (State Nat) ()
-- incr = modify (+1)

newunderscore: StateT Nat (State Nat) NonNullString
newunderscore = lift $ state (\n => (S n, let x = "__underscore'" ++ show n in MkNonNullStr {p=believe_me 1} x))

get_: StateT Nat (State Nat) (Bounds -> WithBounds Nat)
get_ = state (\key => (S key, \b => MkBounded key False b))

span: WithBounds a -> WithBounds b -> Bounds
span (MkBounded _ _ (MkBounds ln0 cl0 _ _)) (MkBounded _ _ (MkBounds _ _ ln1 cl1)) = MkBounds ln0 cl0 ln1 cl1

0 Key: Type
Key = WithBounds Nat

export 
Info Key where 
    (.key) x = NodeKey x.val
    (.span) = WithBounds.(.bounds)
    (.new) x = {isIrrelevant:=True} x

public export
data ParseError: Type where
    ParseErr: (path: String) -> (msg: String) -> Maybe Bounds -> ParseError

public export
data LookAhead: MinCamlTokenKind -> Type where
    MkLookAhead: (kind: MinCamlTokenKind) -> LookAhead kind

0 RT: Type
RT = StateT Nat (State Nat) (WithBounds (Node Key))
0 Tokens: Type
Tokens = (SnocList (WithBounds MinCamlToken), List (WithBounds MinCamlToken))
0 WT: Type
WT = WithBounds MinCamlToken
0 Parser: Type -> Type
Parser = StateT Tokens (ReaderT String (Either ParseError)) 

showEitherName: Either String () -> String
showEitherName (Left s) = s
showEitherName (Right ()) = "_"

argM : Either NonNullString () -> StateT Nat (State Nat) NonNullString 
argM (Left s) = pure s
argM (Right ()) = newunderscore

argsM : Traversable t => t (Either NonNullString ()) -> StateT Nat (State Nat) (t NonNullString)
argsM args = traverse argM args

binaryM: ((key: WithBounds Nat) -> Node Key -> Node Key -> Node Key) -> RT -> RT -> RT
binaryM k e1 e2 = do e1 <- e1; {- incr; -} e2 <- e2; {- incr; -} pure $ MkBounded (k (!get_ (span e1 e2)) e1.val e2.val) False (span e1 e2)
  
fMulM, fDivM, fAddM, fSubM, addM, subM: RT -> RT -> RT

eqM, neqM, ltM, leM, gtM, geM : RT -> RT -> RT

semiM: RT -> RT -> RT

fMulM e1 e2 = binaryM (\key => FMul {key}) e1 e2
fDivM e1 e2 = binaryM (\key => FDiv {key}) e1 e2
fAddM e1 e2 = binaryM (\key => FAdd {key}) e1 e2
fSubM e1 e2 = binaryM (\key => FSub {key}) e1 e2
addM e1 e2 = binaryM (\key => Add {key}) e1 e2
subM e1 e2 = binaryM (\key => Sub {key}) e1 e2
eqM e1 e2 = binaryM (\key => Eq {key}) e1 e2
neqM e1 e2 = binaryM (\key => Neq {key}) e1 e2
ltM e1 e2 = binaryM (\key => Lt {key}) e1 e2
leM e1 e2 = binaryM (\key => Le {key}) e1 e2
gtM e1 e2 = binaryM (\key => Gt {key}) e1 e2
geM e1 e2 = binaryM (\key => Ge {key}) e1 e2
semiM e1 e2 = binaryM (\key => Semi {key}) e1 e2

putM: RT -> RT -> RT -> RT
putM e1 e2 e3 = do 
    e1 <- e1; {- incr -}
    e2 <- e2; {- incr -}
    e3 <- e3; {- incr -}
    pure $ MkBounded (Put e1.val e2.val e3.val {key=(!get_ (span e1 e3))}) False (span e1 e3)

getM: RT -> RT -> RT
getM e1 e2 = do 
    e1 <- e1; {- incr; -} e2 <- e2; {- incr -}
    let get' = (Get e1.val e2.val {key=(!get_ (span e1 e2))})
    pure $ MkBounded get' False (span e1 e2)

lookahead : Parser MinCamlTokenKind
lookahead = do 
    case snd !get of 
        [] => pure EOF
        hd::_ => pure hd.val.kind

lookaheads : List MinCamlTokenKind -> Parser Bool
lookaheads ks = do 
    case snd !get of 
        [] => pure False
        hd::_ => pure $ hd.val.kind `elem` ks

lookaheadN: List MinCamlTokenKind -> Parser Bool
lookaheadN ks = gets (\(_,y) => isPrefixOfBy (\x, y => x == y.val.kind) ks y)

latest: Parser (Maybe WT)
latest = do 
    case fst !get of 
        Lin => pure Nothing
        _ :< x => pure $ Just x


peek : {default 0 k: Nat} -> Parser WT
peek {k} = do 
    case drop k (snd !get) of 
        [] => pure $ MkBounded (Tok EOF "") False (MkBounds 0 0 0 0)
        hd::_ => pure hd

throw: (msg: String) -> Maybe Bounds -> Parser a
throw msg bounds = throwError $ ParseErr !ask msg bounds

any: Parser ()
any = do 
    (sx, ys) <- get
    case (sx, ys) of 
        (_:<x, []) => throw "expected any token after \{x.val.text}, got EOF" (Just x.bounds)
        (Lin, []) => throw "expected any token, got EOF" Nothing
        (_, hd::tl) => modify (\(xs, ys) => (xs :< hd, tl))

bounds: Parser a -> Parser (WithBounds a)
bounds p = do 
    (_, k) <- get 
    a <- p
    (k', _) <- get
    case (k, k') of 
        (tok::_, _:<tok') => pure $ MkBounded a False (span tok tok')
        _ => throw "bounds: unexpected EOF" Nothing

match: {caller: String} -> (k: MinCamlTokenKind) -> Parser (TokType k)
match k = do 
    case !get of 
        (sx, y::ys) => if k == y.val.kind then do put (sx :< y, ys); pure $ tokValue k y.val.text else throw "in `\{caller}`, expected \{show k}, got \{show y.val.text}" (Just y.bounds)
        (_, []) => if k == EOF then pure $ tokValue k "" else throw "in `\{caller}`, expected \{show k}, got EOF" Nothing

match': (ks: List1 MinCamlTokenKind) -> Parser ()
match' ks = do 
    case !get of 
        (_, y::ys) => if y.val.kind `elem` ks then pure () else throw "expected \{joinBy ", " $ show <$> forget ks}, got \{show y.val.text}" (Just y.bounds)
        (_, []) => throw "expected \{joinBy ", " $ show <$> forget ks}, got EOF" Nothing

while: Parser Bool -> Lazy (Parser a) -> Parser (List a)
while cond body = do 
    b <- cond
    if b then do 
        x <- body
        xs <- while cond body
        pure $ x::xs
        else pure []
    
try: Parser a -> Parser a 
try p = do 
    state <- get
    res <- p 
    put state
    pure res

nonnull: Parser String -> Parser NonNullString
nonnull p = do 
    s <- bounds p
    case choose (s.val /= "") of 
        Left p => pure (MkNonNullStr s.val)
        Right _ => throw "null identifier" (Just s.bounds)

parseArg: Parser (Either (WithBounds NonNullString) (WithBounds ()))
parseArg = let match = match {caller="parseArg"} in do
    tok <- peek
    case tok.val.kind of 
        IDENT => Left <$> bounds (nonnull (match IDENT))
        UNDERSOCRE => Right <$> bounds (match UNDERSOCRE)
        EOF => throw "expected <ident> or `_`, got EOF" Nothing
        _ => throw "expected <ident> or `_`, got `\{tok.val.text}`" (Just $ tok.bounds)

checkLinear: List (Either (WithBounds NonNullString) (WithBounds ())) -> Either (WithBounds NonNullString) ()
checkLinear [] = pure ()
checkLinear (Right _::args) = checkLinear args
checkLinear ((Left name)::args) = case find (\x => case x of Left name' => name.val == name'.val; _ => False) args of 
    Nothing => checkLinear args
    Just _ => Left name

extract: Either (WithBounds a) (WithBounds c) -> Either a c
extract (Left x) = Left x.val
extract (Right x) = Right x.val

lookThrough : Parser ()
lookThrough = let match = match {caller="lookThrough"} in do 
    b <- bounds $ match LPAREN
    ignore $ while (not <$> lookaheads [LPAREN, RPAREN, EOF]) any
    case !lookahead of 
        RPAREN => match RPAREN
        LPAREN => do 
            lookThrough
            ignore $ while (not <$> lookaheads [RPAREN, EOF]) any
            match RPAREN
        _ => throw "unclosed `(`" $ (span <$> Just b <*> !latest)

export
[a3] Show (WithBounds MinCamlToken) where
    show (MkBounded tok _ bounds) = "\{show @{a2} bounds}, \{show tok}"

-- match : {default True fatalFlag: Bool} -> (k: MinCamlTokenKind) -> Grammar state MinCamlToken True (TokType k)
-- match k = Text.Parser.match k <|> (do tok <- bounds peek; fail "expected \{show k}, got \{show tok.val.text}")

-- fatalErrorOn : (msg: MinCamlToken -> String) -> (toks: List MinCamlTokenKind) -> Grammar state MinCamlToken False ()
-- fatalErrorOn msg toks = do 
--     tok <- peek
--     when (tok.kind `elem` toks) (fatalError (msg tok))

-- fatalErrorExcept : (msg: MinCamlToken -> String) -> (toks: List MinCamlTokenKind) -> Grammar state MinCamlToken False ()
-- fatalErrorExcept msg toks = do 
--     tok <- peek
--     when (not $ tok.kind `elem` toks) (fatalError (msg tok))

-- %hide Text.Parser.match

mutual
    ||| do not use `eof`, use `match EOF` instead, and remember to append an `EOF` token to the end of the input.
    ||| This is because `peek` will cause an error to be thrown when no more tokens are available.
    toplevel: Parser RT
    toplevel = parseExpr <* match {caller="toplevel"} EOF
    
    parseExpr: Parser RT
    parseExpr = case !lookahead of LET => parseLet; _ => parseSemi

    parseLet: Parser RT
    parseLet = let match = match {caller="parseLet"} in do 
        b <- bounds $ match LET 
        case !lookahead of 
            REC => parseLetRec' b
            LPAREN => parseLetTuple' b
            _ => parseLet' b
    where 
        parseLet': WithBounds () -> Parser RT 
        parseLet' b = let match = match {caller="parseLet'"} in do 
            name <- 
                case !lookahead of 
                    IDENT => Left <$> nonnull (match IDENT)
                    UNDERSOCRE => Right <$> match UNDERSOCRE
                    EOF => throw "expected `let <ident>` or `let _`, got EOF" Nothing
                    _ => throw "expected `let <ident>` or `let _`, got \{show (!peek).val}" (Just $ (!peek).bounds)
            match EQ 
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            pure $ letM b (argM name) e1 e2
            where 
                letM: WithBounds () -> StateT Nat (State Nat) NonNullString -> RT -> RT -> RT
                letM b id e1 e2 = do
                    e1 <- e1; {- incr -}
                    e2 <- e2; {- incr -}
                    pure $ MkBounded (Let !id e1.val e2.val {key=(!get_ (span b e2))}) False (span b e2)
                    -- pure $ (Let !id !newvar e1 e2 {key=(!get)})

        parseLetTuple': WithBounds () -> Parser RT
        parseLetTuple' b = let match = match {caller="parseLetTuple'"} in do
            match LPAREN 
            (_ ** names) <- parseLetTupleArgs
            match RPAREN
            match EQ
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            pure $ letTupleM b (argsM names) e1 e2
        where
            parseLetTupleArgs: Parser (n: Nat ** Vect (2 + n) (Either NonNullString ()))
            parseLetTupleArgs = let match = match {caller="parseLetTupleArgs"} in do
                name0 <- parseArg
                name1 <- match COMMA *> parseArg
                names <- while (lookaheads [COMMA]) (match COMMA *> parseArg)
                tok <- peek
                case tok.val.kind of 
                    RPAREN => case checkLinear (reverse (name0::name1::names)) of 
                        Right _ => pure (_ ** extract <$> (name0 :: name1 :: Vect.fromList names))
                        Left name => throw "duplicate variable `\{name.val}`" (Just $ name.bounds)
                    EOF => throw "expected `,` or `)`, got EOF" Nothing
                    _ => throw "expected `,` or `)`, got \{tok.val.text}" (Just $ tok.bounds)

            letTupleM: {n: Nat} -> WithBounds () -> StateT Nat (State Nat) (Vect (2 + n) NonNullString) -> RT -> RT -> RT
            letTupleM b args e1 e2 = do
                e1 <- e1; {- incr -}
                e2 <- e2; {- incr -}
                pure $ MkBounded (LetTuple !args e1.val e2.val {key=(!get_ (span b e2))}) False (span b e2)
                -- pure $ (LetTuple !args !(newvars $ 2 + n) e1 e2 {key=(!get)})
        
        parseLetRec': WithBounds () -> Parser RT
        parseLetRec' b = let match = match {caller="parseLetRec'"} in do
            match REC
            name <- nonnull $ match IDENT
            arg0 <- parseArg
            args <- while (lookaheads [IDENT, UNDERSOCRE]) parseArg
            match EQ
            e1 <- parseExpr
            match IN
            e2 <- parseExpr
            case checkLinear (reverse (arg0::args)) of 
                Right _ => pure $ letRecM b name (argsM $ extract <$> (arg0::Vect.fromList args)) e1 e2
                Left name => throw "duplicate variable `\{name.val}`" (Just $ name.bounds)
        where 
            letRecM: {n: Nat} -> WithBounds () -> NonNullString -> StateT Nat (State Nat) (Vect (1 + n) NonNullString) -> RT -> RT -> RT
            letRecM {n} b f args e1 e2 = do
            e1 <- e1; {- incr -}
            e2 <- e2; {- incr -}
            pure $ MkBounded (LetRec (MkFunDef (!get_ (span b e1)) f !args e1.val) e2.val {key=(!get_ (span b e2)), nArgs=n}) False (span b e2)

    parseSemi: Parser RT
    parseSemi = do 
        e <- if !lookahead == IF then parseIf else parsePut
        -- info ("parseSemi: lookahead=" ++ show @{a3} !(bounds peek)) pure ()
        if !lookahead == SEMICOLON then parseSemi1 e else pure e
    where 
        parseSemi1: RT -> Parser RT
        parseSemi1 e1 = let match = match {caller="parseSemi1"} in do
            match SEMICOLON
            e2 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parsePut
            e2 <- case !lookahead of SEMICOLON => parseSemi1 e2; _ => pure e2
            pure $ semiM e1 e2

    parseIf: Parser RT
    parseIf = let match = match {caller="parseIf"} in do 
        b <- bounds $ match IF
        e1 <- parseExpr
        match THEN 
        e2 <- parseExpr
        match ELSE 
        e3 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parsePut
        pure $ ifM b e1 e2 e3
        where 
            ifM: WithBounds () -> RT -> RT -> RT -> RT
            ifM b e1 e2 e3 = do 
                e1 <- e1; {- incr -}
                e2 <- e2; {- incr -}
                e3 <- e3; {- incr -}
                pure $ MkBounded (If e1.val e2.val e3.val {key=(!get_ (span b e3))}) False (span b e3)
    
    parsePut: Parser RT
    parsePut = do 
        if !isPutLhs then do lhs <- parsePutLhs; parsePutRhs lhs else parseTuple
    where  
        ||| skip over consecutive `(...)` and `.(exp)` to see if the next token is `<-`
        isPutLhs, isPutLhs': Parser Bool
        isPutLhs = do
            s <- get
            res <- case !lookahead of 
                LPAREN => lookThrough *> (do if !lookahead == DOT then isPutLhs' else pure False)
                IDENT => match {caller="isPutLhs"} IDENT *> (do if !lookahead == DOT then isPutLhs' else pure False)
                _ => pure False
            put s
            pure res
        isPutLhs' = do
            match {caller="isPutLhs'"} DOT
            lookThrough
            case !lookahead of 
                DOT => isPutLhs'
                ASSIGN => pure True
                _ => pure False
        
        parsePutLhs: Parser (RT -> RT)
        parsePutLhs = let match = match {caller="parsePutLhs"} in do
            e1 <- parseAtomic
            e2 <- match DOT *> match LPAREN *> parseExpr <* match RPAREN
            e2s <- while (lookaheads [DOT]) (do match DOT; match LPAREN; parseExpr <* match RPAREN)
            let (e2s, e2) = unsnoc (e2:::e2s)
            let e1 = foldl getM e1 e2s
            pure $ \rhs => putM e1 e2 rhs
        parsePutRhs: (RT -> RT) -> Parser RT
        parsePutRhs lhs = do
            match {caller="parsePutRhs"} ASSIGN
            rhs <- case !lookahead of LET => parseLet; IF => parseIf; _ => if !isPutLhs then do lhs' <- parsePutLhs; parsePutRhs lhs' else parseTuple
            pure $ lhs rhs

    parseTuple: Parser RT
    parseTuple = do 
        e0 <- parseCmp
        if !lookahead == COMMA then parseTuple1 e0 else pure e0
    where 
        parseTuple1: RT -> Parser RT
        parseTuple1 e0 = let match = match {caller="parseTuple1"} in do
            e1 <- match COMMA *> parseTupleArg
            es <- while (lookaheads [COMMA]) (match COMMA *> parseTupleArg)
            pure $ tupleM (e0::e1::Vect.fromList es)
        where 
            parseTupleArg: Parser RT
            parseTupleArg = do 
                case !lookahead of 
                    LET => parseLet
                    IF => parseIf
                    INT => parseCmp
                    FLOAT => parseCmp
                    IDENT => parseCmp
                    LPAREN => parseCmp
                    BOOL => parseCmp
                    _ => throw "expected expression, got \{show !(peek)}" (Just $ (!peek).bounds)
            tupleM: {n: Nat} -> Vect (2 + n) RT -> RT 
            tupleM {n} es = do 
                es <- traverse id es; Prelude.pure $ MkBounded (Tuple (val <$> es) {key=(!get_ (span (head es) (last es)))}) False (span (head es) (last es))

    parseCmp: Parser RT
    parseCmp = let match = match {caller="parseCmp"} in do
        e <- parseAddSub
        case !lookahead of 
            EQ => parseCmp1 e (match EQ) eqM
            NEQ => parseCmp1 e (match NEQ) neqM
            LT => parseCmp1 e (match LT) ltM
            LE => parseCmp1 e (match LE) leM
            GT => parseCmp1 e (match GT) gtM
            GE => parseCmp1 e (match GE) geM
            _ => pure e
    where 
        parseCmp1: RT -> Parser () -> (RT -> RT -> RT) -> Parser RT
        parseCmp1 e1 match' m = let match = match {caller="parseCmp1"} in do
            match'
            e2 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseAddSub
            e <- pure $ m e1 e2
            case !lookahead of 
                EQ => parseCmp1 e (match EQ) eqM
                NEQ => parseCmp1 e (match NEQ) neqM
                LT => parseCmp1 e (match LT) ltM
                LE => parseCmp1 e (match LE) leM
                GT => parseCmp1 e (match GT) gtM
                GE => parseCmp1 e (match GE) geM
                _ => pure e

    parseAddSub: Parser RT
    parseAddSub = let match = match {caller="parseAddSub"} in do
        e <- parseMulDiv
        case !lookahead of 
            ADD => parseAddSub1 e (match ADD) addM
            MINUS => parseAddSub1 e (match MINUS) subM
            FADD => parseAddSub1 e (match FADD) fAddM
            FMINUS => parseAddSub1 e (match FMINUS) fSubM
            _ => pure e
    where 
        parseAddSub1: RT -> Parser () -> (RT -> RT -> RT) -> Parser RT
        parseAddSub1 e1 match' m = let match = match {caller="parseAddSub1"} in do
            match'
            e2 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseMulDiv
            e <- pure $ m e1 e2
            case !lookahead of 
                ADD => parseAddSub1 e (match ADD) addM
                MINUS => parseAddSub1 e (match MINUS) subM
                FADD => parseAddSub1 e (match FADD) fAddM
                FMINUS => parseAddSub1 e (match FMINUS) fSubM
                _ => pure e

    parseMulDiv: Parser RT
    parseMulDiv = do 
        e <- parseUnary
        case !lookahead of 
            FMUL => parseFMul1 e
            FDIV => parseFDiv1 e
            _ => pure e
    where 
        parseFMul1, parseFDiv1: RT -> Parser RT

        parseFMul1 e1 = do 
            match {caller="parseFMul1"} FMUL
            e2 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseUnary
            e <- pure $ fMulM e1 e2
            case !lookahead of 
                FMUL => parseFMul1 e
                FDIV => parseFDiv1 e
                _ => pure e
        
        parseFDiv1 e1 = do 
            match {caller="parseFDiv1"} FDIV
            e2 <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseUnary
            e <- pure $ fDivM e1 e2
            case !lookahead of 
                FMUL => parseFMul1 e
                FDIV => parseFDiv1 e
                _ => pure e

    parseUnary: Parser RT
    parseUnary = do 
        case !lookahead of 
            MINUS => parseNeg
            FMINUS => parseFNeg
            _ => parseApp
    where
        parseNeg, parseFNeg: Parser RT
        parseNeg = do 
            b <- bounds (match {caller="parseNeg"} MINUS)
            e <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseUnary
            pure $ negM b e
            where 
                negM: WithBounds () -> RT -> RT
                negM b e = do 
                    e <- e; {- incr -}
                    let span = span b e
                    case e.val of 
                        F _ => pure $ MkBounded (FNeg e.val {key=(!get_ span)}) False span
                        _ => pure $ MkBounded (Neg e.val {key=(!get_ span)}) False span

        parseFNeg = do 
            b <- bounds (match {caller="parseFNeg"} FMINUS)
            e <- case !lookahead of LET => parseLet; IF => parseIf; _ => parseUnary
            pure $ fNegM b e
            where 
                fNegM: WithBounds () -> RT -> RT
                fNegM b e = do 
                    e <- e; {- incr; -} pure $ MkBounded (FNeg e.val {key=(!get_ (span b e))}) False (span b e)

    parseApp: Parser RT
    parseApp = do 
        e <- parseGet
        if !(lookaheads [INT, FLOAT, IDENT, LPAREN, BOOL]) then parseApp1 e else pure e
    where 
        parseApp1: RT -> Parser RT
        parseApp1 e1 = do 
            arg0 <- if !(lookaheads [INT, FLOAT, IDENT, LPAREN, BOOL]) then parseGet else throw "when parsing application, expected expression, got \{show !(peek)}" (Just $ (!peek).bounds)
            args <- while (lookaheads [INT, FLOAT, IDENT, LPAREN, BOOL]) parseGet
            when !(lookaheads [LET, IF, UNDERSOCRE, ASSIGN, REC, DOT]) (throw "when parsing application, unexpected \{show !(peek)}" (Just $ (!peek).bounds))
            e <- pure $ appM e1 (arg0:::args)
            if !(lookaheads [INT, FLOAT, IDENT, LPAREN, BOOL]) then parseApp1 e else pure e
        where 
            appM: RT -> List1 RT -> RT
            appM f args = do 
                f <- f; arg0:::args'' <- args'; {- incr; -} 
                let span = span f (last (arg0::args''))
                let app = (App f.val (val <$> arg0::Vect.fromList args'') {key=(!get_ span)})
                pure $ MkBounded app False span
            where 
                args' : StateT Nat (State Nat) (List1 (WithBounds (Node Key)))
                args' = traverse (\x => {- incr >> -} x) args

    parseGet: Parser RT
    parseGet = do 
        e <- parseAtomic
        if !lookahead == DOT then parseGet1 e else pure e
    where 
        parseGet1: RT -> Parser RT
        parseGet1 e1 = let match = match {caller="parseGet1"} in do
            match DOT
            match LPAREN
            e <- parseExpr
            match RPAREN
            e <- pure $ getM e1 e
            if !lookahead == DOT then parseGet1 e else pure e

    parseAtomic: Parser RT
    parseAtomic = do 
        case !lookahead of
            INT => parseInt
            FLOAT => parseFloat
            IDENT => parseIdent
            LPAREN => parseParen
            BOOL => parseBool
            _ => throw "expected atomic expression, got \{show !(peek)}" (Just $ (!peek).bounds) 
    where 
        parseInt, parseFloat, parseIdent, parseParen, parseBool: Parser RT
        parseInt = do 
            i <- bounds (match {caller="parseInt"} INT)
            -- info "parseInt matched \{i}" $ 
            case parseInteger i.val of 
                Nothing => throw "illegal integer literal: \{i.val}" (Just i.bounds)
                Just x => pure $ intM (const x <$> i)
            where 
                intM: WithBounds Int -> RT
                intM i = pure $ MkBounded (I i.val {key=(!get_ i.bounds)}) False i.bounds

        parseFloat = do
            f <- bounds (match {caller="parseFloat"} FLOAT)
            case parseDouble f.val of 
                Nothing => throw "illegal float literal: \{f.val}" (Just f.bounds)
                Just x => pure $ floatM (const x <$> f)
            where 
                floatM: WithBounds Double -> RT
                floatM f = pure $ MkBounded (F f.val {key=(!get_ f.bounds)}) False f.bounds
        parseIdent = do 
            name <- bounds (nonnull (match {caller="parseIdent"} IDENT))
            pure $ identM name
            where 
                identM: (name: WithBounds NonNullString) -> RT
                identM name = pure $ MkBounded (Var name.val {key=(!get_ name.bounds)}) False name.bounds

        parseParen = do 
            b <- bounds (match {caller="parseParen"} LPAREN)
            e <- case !lookahead of RPAREN => parseUnit b; _ => parseExpr <* match {caller="parseParen"} RPAREN
            pure e
            where 
                parseUnit: WithBounds () -> Parser RT
                parseUnit b = do 
                    b' <- bounds (match {caller="parseUnit"} RPAREN)
                    pure $ unitM b b'
                where 
                    unitM: WithBounds () -> WithBounds () -> RT
                    unitM b b' = pure $ MkBounded (U {key=(!get_ (span b b'))}) False (span b b')

        parseBool = do 
            b <- bounds (match {caller="parseBool"} BOOL)
            pure $ boolM b
            where 
                boolM: WithBounds Bool -> RT
                boolM b = pure $ MkBounded (B b.val {key=(!get_ b.bounds)}) False b.bounds

export 
Show ParseError where 
    show (ParseErr path msg Nothing) = "File \{show path}, <unkown location>\n\{msg}"
    show (ParseErr path msg (Just (MkBounds ln0 cl0 ln1 cl1))) =
        let line = prefix' ln0 ln1 "line" "lines" in
        let character = prefix' cl0 cl1 "character" "characters" in """
        File \{show path}, \{line}, \{character}
        \{msg}
        """
    where
        prefix': (start: Int) -> (end: Int) -> (singular: String) -> (plural: String) -> String 
        prefix' start end singular plural = if start == end then "\{singular} \{show (start+1)}" else "\{plural} \{show (start+1)}-\{show (end+1)}" 

-- fromParsingError: String -> ParsingError MinCamlToken -> ParseError
-- fromParsingError path (Error msg bounds) = ParseErr path msg bounds

parseImpl : {path: String} -> (toks: List1 (WithBounds MinCamlToken)) -> Either ParseError RT
parseImpl {path} toks = do
  let toks = filter (not . ignored) (forget toks)
  ((consumed, unconsumed), res) <- runReaderT path (runStateT (Lin, toks) toplevel)
  case unconsumed of
    [] => pure res
    hd::_ => throwError (ParseErr path "unconsumed token `\{show @{a3} hd}`" (Just $ bounds hd))

export
parse : {default "<string>" path: String} -> String -> Either LexError (Either ParseError (Node Key))
parse {path} x = do 
    res <- parseImpl {path} <$> lexMinCaml x
    case res of 
        Left err => pure $ Left err
        Right res => do 
            let (_, _, node) = runIdentity $ runStateT Z (runStateT Z res)
            pure $ Right node.val
-- where convert: Functor f => (a -> b) -> Either (f a) c -> Either (f b) c
--       convert f x = mapFst (f <$>) x

parseString: String -> IO ()
parseString str = do 
    case parse str of
        Left err => putStrLn "File <string>, \{show err}" 
        Right (Left err) => putStrLn (show err)
        Right (Right node) => putStrLn $ show node


