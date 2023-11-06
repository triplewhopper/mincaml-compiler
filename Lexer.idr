module Lexer
import Data.List
import Data.List1
import Text.Lexer
import Data.String
import Data.Vect

%default total 

public export
data MinCamlTokenKind = 
    ADD | MINUS | FADD | FMINUS | FMUL | FDIV | EQ | NEQ | UNDERSOCRE 
    | LT | LE | GT | GE | ASSIGN | IF | THEN | ELSE | LET | REC | IN 
    | LPAREN | RPAREN | SEMICOLON | SPACES | COMMENT
    | COMMA | DOT | EOF | INT | FLOAT | BOOL | UNIT | IDENT

public export
MinCamlToken : Type
MinCamlToken = Token MinCamlTokenKind

export
Eq MinCamlTokenKind where
    (==) ADD ADD = True
    (==) MINUS MINUS = True
    (==) FADD FADD = True
    (==) FMINUS FMINUS = True
    (==) FMUL FMUL = True
    (==) FDIV FDIV = True
    (==) EQ EQ = True
    (==) NEQ NEQ = True
    (==) UNDERSOCRE UNDERSOCRE = True
    (==) LT LT = True
    (==) LE LE = True
    (==) GT GT = True
    (==) GE GE = True
    (==) ASSIGN ASSIGN = True
    (==) IF IF = True
    (==) THEN THEN = True
    (==) ELSE ELSE = True
    (==) LET LET = True
    (==) REC REC = True
    (==) IN IN = True
    -- (==) ARRAY_CREATE ARRAY_CREATE = True
    -- (==) NOT NOT = True
    (==) LPAREN LPAREN = True
    (==) RPAREN RPAREN = True
    (==) SEMICOLON SEMICOLON = True
    (==) COMMA COMMA = True
    (==) DOT DOT = True
    (==) EOF EOF = True
    (==) INT INT = True
    (==) FLOAT FLOAT = True
    (==) BOOL BOOL = True
    (==) UNIT UNIT = True
    (==) IDENT IDENT = True
    (==) COMMENT COMMENT = True
    (==) SPACES SPACES = True
    (==) _ _ = False

export 
Show MinCamlTokenKind where
    show ADD = "ADD"
    show MINUS = "MINUS"
    show FADD = "FADD"
    show FMINUS = "FMINUS"
    show FMUL = "FMUL"
    show FDIV = "FDIV"
    show EQ = "EQ"
    show NEQ = "NEQ"
    show UNDERSOCRE = "UNDERSOCRE"
    show LT = "LT"
    show LE = "LE"
    show GT = "GT"
    show GE = "GE"
    show ASSIGN = "ASSIGN"
    show IF = "IF"
    show THEN = "THEN"
    show ELSE = "ELSE"
    show LET = "LET"
    show REC = "REC"
    show IN = "IN"
    -- show ARRAY_CREATE = "ARRAY_CREATE"
    -- show NOT = "NOT"
    show LPAREN = "LPAREN"
    show RPAREN = "RPAREN"
    show SEMICOLON = "SEMICOLON"
    show COMMA = "COMMA"
    show DOT = "DOT"
    show EOF = "EOF"
    show INT = "INT"
    show FLOAT = "FLOAT"
    show BOOL = "BOOL"
    show UNIT = "UNIT"
    show IDENT = "IDENT"
    show COMMENT = "COMMENT"
    show SPACES = "SPACES"

export
Show MinCamlToken where 
    show (Tok kind text) = """
    \{show text} as \{show kind}
    """

export
TokenKind MinCamlTokenKind where 
    TokType INT = String
    TokType FLOAT = String
    TokType BOOL = Bool
    TokType UNIT = Unit
    TokType IDENT = String
    TokType COMMENT = String
    TokType _ = ()

    tokValue INT s = s
    tokValue FLOAT s = s
    tokValue BOOL s = s == "true"
    tokValue UNIT _ = ()
    tokValue IDENT s = s
    tokValue ADD _ = ()
    tokValue MINUS _ = ()
    tokValue FADD _ = ()
    tokValue FMINUS _ = ()
    tokValue FMUL _ = ()
    tokValue FDIV _ = ()
    tokValue EQ _ = ()
    tokValue NEQ _ = ()
    tokValue UNDERSOCRE _ = ()
    tokValue LT _ = ()
    tokValue LE _ = ()
    tokValue GT _ = ()
    tokValue GE _ = ()
    tokValue ASSIGN _ = ()
    tokValue IF _ = ()
    tokValue THEN _ = ()
    tokValue ELSE _ = ()
    tokValue LET _ = ()
    tokValue REC _ = ()
    tokValue IN _ = ()
    -- tokValue ARRAY_CREATE _ = ()
    -- tokValue NOT _ = ()
    tokValue LPAREN _ = ()
    tokValue RPAREN _ = ()
    tokValue SEMICOLON _ = ()
    tokValue COMMA _ = ()
    tokValue DOT _ = ()
    tokValue EOF _ = ()
    tokValue COMMENT s = s
    tokValue SPACES _ = ()

export
ignored : WithBounds MinCamlToken -> Bool
ignored (MkBounded (Tok SPACES _) _ _) = True
ignored (MkBounded (Tok COMMENT _) _ _) = True
ignored _ = False

identifier : Lexer
identifier = ((is '_' <|> alpha) <+> some (is '\'' <|> is '_' <|> alphaNum)) <|> alpha

array_create: Lexer
array_create = exact "Array" <+> many space <+> is '.' <+> many space <+> (exact "create" <|> exact "make")

integralPart, fractionalPart, exponentialPart: Lexer

integralPart = digit <+> many (is '_' <|> digit)
fractionalPart = some (is '_' <|> digit)
exponentialPart = approx "e" <+> opt (oneOf "+-") <+> digit <+> many (is '_' <|> digit)

floatLit : Lexer
floatLit = (
  (integralPart <+> is '.' <+> fractionalPart <+> opt exponentialPart) <|> 
  (is '.' <+> fractionalPart <+> opt exponentialPart) <|>
  (integralPart <+> opt (is '.') <+> exponentialPart) <|>
  (integralPart <+> is '.' <+> opt exponentialPart))
  
comment : Lexer 
comment = exact "(*" <+> manyUntil (exact "(*" <|> exact "*)") any <+> (exact "*)" <|> (comment <+> manyThen (exact "*)") any))

keywords : List (String, MinCamlTokenKind)
keywords = [
  ("let", LET),
  ("rec", REC),
  ("if", IF),
  ("then", THEN),
  ("else", ELSE),
  ("in", IN),
  ("true", BOOL),
  ("false", BOOL)
  -- ("not", NOT)
]

minCamlTokenMap : TokenMap MinCamlToken
minCamlTokenMap = toTokenMap [(spaces, SPACES), (comment, COMMENT), (array_create, IDENT)] ++
  [(identifier, \s =>
      case lookup s keywords of
        (Just kind) => Tok kind s
        Nothing => Tok IDENT s
    ),
    (floatLit, \s => Tok FLOAT s),
    (digitsUnderscoredLit, \s => Tok INT s)
  ] ++ toTokenMap [
    (exact "*.", FMUL),
    (exact "/.", FDIV),
    (exact "+.", FADD),
    (exact "-.", FMINUS),
    (exact "+", ADD),
    (exact "-", MINUS),
    (exact "<=", LE),
    (exact "<>", NEQ),
    (exact ">=", GE),
    (exact "<-", ASSIGN),
    (exact "=", EQ),
    (exact "<", LT),
    (exact ">", GT),
    (exact "(", LPAREN),
    (exact ")", RPAREN),
    (exact ";", SEMICOLON),
    (exact ",", COMMA),
    (exact ".", DOT),
    (exact "_", UNDERSOCRE)
  ]

public export
data LexError: Type where
  LexErr: Int -> Int -> LexError

export
Show LexError where
  show (LexErr ln cl) = "line \{show (ln + 1)}, character \{show (cl + 1)}"

||| Lexes a string into a list of tokens.
||| garantees that the last token is EOF.
export
lexMinCaml : String -> Either LexError (List1 (WithBounds MinCamlToken))
lexMinCaml str =
  case lex minCamlTokenMap str of
    (tokens, ln, cl, "") => Right (reverse (MkBounded (Tok EOF "") False (MkBounds ln cl ln cl):::reverse tokens))
    (tokens, ln, cl, rest) => Left (LexErr ln cl)


