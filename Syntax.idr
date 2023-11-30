module Syntax

import Data.Vect
import Data.String
import Text.Lexer
import Data.Vect.Quantifiers
import Data.So
import Data.DPair
import Control.Function
import Decidable.Equality
import Ty
import NonNullString
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util


public export
data SyntaxError: Type where
    SyntaxErr: String -> SyntaxError

mutual
    public export
    record FunDef (a: Type) (nArgs: Nat) where
        constructor MkFunDef
        key: a
        name: NonNullString
        -- ty: TypeVar
        args: Vect (1 + nArgs) NonNullString
        -- argsTy: Vect (1 + nArgs) TypeVar
        body: Node a

    public export
    data Node: Type -> Type where
        U: {key: a} -> Node a
        I: {key: a} -> Int -> Node a
        B: {key: a} -> Bool -> Node a
        F: {key: a} -> Double -> Node a
        Var: {key: a} -> (name: NonNullString) -> Node a

        Get: {key: a} -> Node a -> Node a -> Node a

        Neg: {key: a} -> Node a -> Node a
        FNeg: {key: a} -> Node a -> Node a

        App: {key: a} -> {n: Nat} -> Node a -> Vect (1 + n) (Node a) -> Node a

        FMul: {key: a} -> Node a -> Node a -> Node a
        FDiv: {key: a} -> Node a -> Node a -> Node a

        FAdd: {key: a} -> Node a -> Node a -> Node a
        FSub: {key: a} -> Node a -> Node a -> Node a
        Add: {key: a} -> Node a -> Node a -> Node a
        Sub: {key: a} -> Node a -> Node a -> Node a

        Eq: {key: a} -> Node a -> Node a -> Node a
        Neq: {key: a} -> Node a -> Node a -> Node a
        Lt: {key: a} -> Node a -> Node a -> Node a
        Le: {key: a} -> Node a -> Node a -> Node a
        Gt: {key: a} -> Node a -> Node a -> Node a
        Ge: {key: a} -> Node a -> Node a -> Node a

        Tuple: {key: a} -> {n: Nat} -> Vect (2 + n) (Node a) -> Node a

        Put: {key: a} -> Node a -> Node a -> Node a -> Node a

        If: {key: a} -> Node a -> Node a -> Node a -> Node a

        Semi: {key: a} -> Node a -> Node a -> Node a

        Let: {key: a} -> (x: NonNullString) ->  Node a -> Node a -> Node a
        LetRec: {key: a} -> {nArgs: Nat} -> FunDef a nArgs -> Node a -> Node a
        LetTuple: {key: a} -> {n: Nat} -> Vect (2 + n) NonNullString -> Node a -> Node a -> Node a

export
(.getKey): Node a -> a
(.getKey) (U {key}) = key
(.getKey) (I {key} _) = key
(.getKey) (B {key} _) = key
(.getKey) (F {key} _) = key
(.getKey) (Var {key} _) = key
(.getKey) (Get {key} _ _) = key
(.getKey) (Neg {key} _) = key
(.getKey) (FNeg {key} _) = key
(.getKey) (App {key} _ _) = key
(.getKey) (FMul {key} _ _) = key
(.getKey) (FDiv {key} _ _) = key
(.getKey) (FAdd {key} _ _) = key
(.getKey) (FSub {key} _ _) = key
(.getKey) (Add {key} _ _) = key
(.getKey) (Sub {key} _ _) = key
(.getKey) (Eq {key} _ _) = key
(.getKey) (Neq {key} _ _) = key
(.getKey) (Lt {key} _ _) = key
(.getKey) (Le {key} _ _) = key
(.getKey) (Gt {key} _ _) = key
(.getKey) (Ge {key} _ _) = key
(.getKey) (Tuple {key} _) = key
(.getKey) (Put {key} _ _ _) = key
(.getKey) (If {key} _ _ _) = key
(.getKey) (Semi {key} _ _) = key
(.getKey) (Let {key} _ _ _) = key
(.getKey) (LetRec {key} _ _) = key
(.getKey) (LetTuple {key} _ _ _) = key

-- export 
-- Functor Node where 
--     map f (U {key}) = U {key=f key}
--     map f (I {key} x) = I {key=f key} x
--     map f (B {key} x) = B {key=f key} x
--     map f (F {key} x) = F {key=f key} x
--     map f (Var {key} x) = Var {key=f key} x
--     map f (Get {key} n1 n2) = Get {key=f key} (map f n1) (map f n2)
--     map f (Neg {key} n) = Neg {key=f key} (map f n)
--     map f (FNeg {key} n) = FNeg {key=f key} (map f n)
--     map f (App {key} n1 ns) = App {key=f key} (map f n1) (map (map f) ns)
--     map f (FMul {key} n1 n2) = FMul {key=f key} (map f n1) (map f n2)
--     map f (FDiv {key} n1 n2) = FDiv {key=f key} (map f n1) (map f n2)
--     map f (FAdd {key} n1 n2) = FAdd {key=f key} (map f n1) (map f n2)
--     map f (FSub {key} n1 n2) = FSub {key=f key} (map f n1) (map f n2)


showU: Show a => Nat -> a -> String 
showU x = assert_total showPrec (User x)

prettyU: Pretty a => Nat -> a -> Doc ann
prettyU x = assert_total prettyPrec (User x)

forceParen: Bool 
forceParen = False
forceTyVar: Bool
forceTyVar = True

isSingle: Node a -> Bool 
isSingle U = True
isSingle (I _) = True
isSingle (B _) = True
isSingle (F _) = True
isSingle (Var _) = True
isSingle _ = False

export
Pretty (Node a) where
    prettyPrec d U = pretty ()
    prettyPrec d (I i) = pretty i
    prettyPrec d (B b) = if b then pretty "true" else pretty "false"
    prettyPrec d (F f) = pretty f
    prettyPrec d (Var x) = pretty x

    prettyPrec d (Get n1 n2) = prettyU 24 n1 <+> ".(" <+> prettyU 24 n2 <+> ")"

    prettyPrec d (App n1 n2s) = parenthesise (forceParen || d > User 22) (hsep (prettyPrec (User 23) <$> toList (n1::n2s)))
    -- prettyPrec d (Array n1 n2) = prettyParens (forceParen || d > User 22) "Array.create" <+> prettyPrec (User 23) n1 <+> prettyPrec (User 23) n2

    prettyPrec d (Neg n) = parenthesise (forceParen || d > User 20) ("-" <++> prettyU 21 n)
    prettyPrec d (FNeg n) = parenthesise (forceParen || d > User 20) ("-." <++> prettyU 21 n)

    prettyPrec d (FMul n1 n2) = parenthesise (forceParen || d > User 18) (prettyU 18 n1 <++> "*." <++> prettyU 18 n2)
    prettyPrec d (FDiv n1 n2) = parenthesise (forceParen || d > User 18) (prettyU 18 n1 <++> "/." <++> prettyU 19 n2)

    prettyPrec d (FAdd n1 n2) = parenthesise (forceParen || d > User 16) (prettyU 16 n1 <++> "+." <++> prettyU 16 n2)
    prettyPrec d (FSub n1 n2) = parenthesise (forceParen || d > User 16) (prettyU 16 n1 <++> "-." <++> prettyU 17 n2)
    prettyPrec d (Add n1 n2) = parenthesise (forceParen || d > User 16) (prettyU 16 n1 <++> "+" <++> prettyU 16 n2)
    prettyPrec d (Sub n1 n2) = parenthesise (forceParen || d > User 16) (prettyU 16 n1 <++> "-" <++> prettyU 17 n2)

    prettyPrec d (Eq n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> "=" <++> prettyU 15 n2)
    prettyPrec d (Neq n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> "<>" <++> prettyU 15 n2)
    prettyPrec d (Lt n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> "<" <++> prettyU 15 n2)
    prettyPrec d (Le n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> "<=" <++> prettyU 15 n2)
    prettyPrec d (Gt n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> ">" <++> prettyU 15 n2)
    prettyPrec d (Ge n1 n2) = parenthesise (forceParen || d > User 14) (prettyU 15 n1 <++> ">=" <++> prettyU 15 n2)

    prettyPrec d (Tuple ns) = tupled (prettyU 13 <$> toList ns)

    prettyPrec d (Put n1 n2 n3) = parenthesise (forceParen || d > User 10) (nest 2 (prettyU 11 n1 <+> ".(" <+> prettyU 11 n2 <+> ")" <++> "<-" <+> softline <+> group(prettyU 11 n2)))


    prettyPrec d (If n1 n2 n3) = parenthesise (forceParen || d > User 8) doc
    where 
        p1, p2, p3: Doc ann 
        p1 = prettyU 9 n1
        p2 = prettyU 8 n2
        p3 = prettyU 8 n3
        doc: Doc ann
        doc = 
            if isSingle n2 then 
                if isSingle n3 then "if" <++> p1 <++> "then" <++> p2 <++> "else" <++> p3
                else (align . sep) [nest 2 ("if" <++> p1 <++> "then" <++> p2), nest 2 ("else" <+> line <+> p3)]
            else if isSingle n3 then (align . sep) [nest 2 ("if" <++> p1 <++> "then" <+> line <+> p2),  "else" <++> p3]
            else (align . sep) [nest 2 ("if" <++> p1 <++> "then" <+> line <+> p2 <++> "else"),  p3]

    prettyPrec d (Semi n1 n2) = parenthesise (forceParen || d > User 6) (align (prettyU 7 n1 <+> semi <+> line <+>prettyU 6 n2))

    prettyPrec d (Let x n1 n2) = parenthesise (forceParen || d > User 4) doc2
    where 
        p1, p2: Doc ann 
        p1 = prettyU 5 n1
        p2 = prettyU 4 n2
        doc1, doc2, doc3, doc4: Doc ann 
        doc1 = "let" <++> pretty x <++> "=" <++> p1 <++> "in" <++> p2
        doc2 = (align . sep) [nest 2 ("let" <++> pretty x <++> "=" <+> softline <+> p1 <++> "in"), p2]
        doc3 = (align . sep) [nest 2 ("let" <++> pretty x <++> "=" <+> softline <+> p1), nest 2 ("in" <+> softline <+> p2)]
        -- doc4 = (align . vsep) [nest 2 ("let" <++> pretty x <++> "=" <+> softline <+> p1), "in",  p2]
                

    prettyPrec d (LetRec f n2) = parenthesise (forceParen || d > User 4) doc2
    where 
        func, pbody, p2: Doc ann
        pbody = prettyU 5 f.body
        p2 = prettyU 4 n2
        func = "let rec" <++> pretty f.name <++> hsep (pretty <$> toList f.args) <++> "="
        doc1, doc2, doc3: Doc ann
        doc1 = func <++> pbody <++> "in" <++> p2
        doc2 = (align . sep) [nest 2 (func <+> line <+> prettyU 4 f.body <++> "in"), p2]
        doc3 = (align . sep) [nest 2 (func <+> line <+> prettyU 4 f.body), nest 2 ("in" <+> softline <+> p2)]

    prettyPrec d (LetTuple xs n1 n2) = parenthesise (forceParen || d > User 4) doc
    where 
        doc: Doc ann 
        doc = (align . sep) [nest 2 ("let" <++> tupled (pretty <$> toList xs) <++> "=" <+> softline <+> prettyU 5 n1 <++> "in"), prettyU 4 n2]
export
Show (Node a) where 
    -- showPrec _ U = "()"
    -- showPrec _ (I i) = show i
    -- showPrec _ (B b) = if b then "true" else "false"
    -- showPrec _ (F f) = show f
    -- showPrec _ (Var x) = x

    -- showPrec _ (Get n1 n2) = "\{assert_total showU 24 n1}.(\{assert_total showU 0 n2})"

    -- -- showPrec d (Not n) = showParens (forceParen || d > User 22) "not \{assert_total showU 23 n}"
    -- showPrec d (App n1 n2s) = showParens (forceParen || d > User 22) "\{assert_total showU 22 n1} \{joinBy " " $ toList $ assert_total showU 23 <$> n2s}"
    -- -- showPrec d (Array n1 n2) = showParens (forceParen || d > User 22) "Array.create \{assert_total showU 23 n1} \{assert_total showU 23 n2}"

    -- showPrec d (Neg n) = showParens (forceParen || d > User 20) "-\{assert_total showU 21 n}"
    -- showPrec d (FNeg n) = showParens (forceParen || d > User 20) "-.\{assert_total showU 21 n}"

    -- showPrec d (FMul n1 n2) = showParens (forceParen || d > User 18) "\{assert_total showU 18 n1} *. \{assert_total showU 18 n2}"
    -- showPrec d (FDiv n1 n2) = showParens (forceParen || d > User 18) "\{assert_total showU 18 n1} /. \{assert_total showU 19 n2}"

    -- showPrec d (FAdd n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} +. \{assert_total showU 16 n2}"
    -- showPrec d (FSub n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} -. \{assert_total showU 17 n2}"
    -- showPrec d (Add n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} + \{assert_total showU 16 n2}"
    -- showPrec d (Sub n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} - \{assert_total showU 17 n2}"

    -- showPrec d (Eq n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} = \{assert_total showU 15 n2}"
    -- showPrec d (Neq n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} <> \{assert_total showU 15 n2}"
    -- showPrec d (Lt n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} < \{assert_total showU 15 n2}"
    -- showPrec d (Le n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} <= \{assert_total showU 15 n2}"
    -- showPrec d (Gt n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} > \{assert_total showU 15 n2}"
    -- showPrec d (Ge n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} >= \{assert_total showU 15 n2}"

    -- -- showPrec d (Tuple ns ts) = 
    -- --     if forceTyVar then showParens True "(\{joinBy ", " $ toList $ assert_total showU 13 <$> ns}): (\{joinBy " * " $ toList $ assert_total showU 13 <$> ts})"
    -- --       else showParens True "\{joinBy ", " $ toList $ assert_total showU 13 <$> ns}"
    -- showPrec d (Tuple ns) = showParens True "\{joinBy ", " $ toList $ assert_total showU 13 <$> ns}"

    -- showPrec d (Put n1 n2) = showParens (forceParen || d > User 10) "\{assert_total showU 11 n1} <- \{assert_total showU 11 n2}"

    -- showPrec d (If n1 n2 n3) = showParens (forceParen || d > User 8) "if \{s1} then \{s2} else \{s3}"
    -- where s1, s2, s3: String
    --       s1 = assert_total showU 9 n1
    --       s2 = assert_total showU 8 n2
    --       s3 = assert_total showU 8 n3

    -- showPrec d (Semi n1 n2) = showParens (forceParen || d > User 6) "\{assert_total showU 7 n1}; \{assert_total showU 6 n2}"

    -- showPrec d (Let x n1 n2) = showParens (forceParen || d > User 4) "let \{x} = \{s1} in \{s2}" 
    -- where s1, s2: String
    --       s1 = assert_total showU 5 n1
    --       s2 = assert_total showU 4 n2
    --     -- if forceTyVar then 
    --     --     showParens (forceParen || d > User 4) "let \{x}: \{t} = \{assert_total showU 5 n1} in\n\{assert_total showU 4 n2}"
    --     --   else 

    -- showPrec d (LetRec f n2) = showParens (forceParen || d > User 4) "let rec \{f.name} \{args} = \{body} in \{s2}" 
    --     where args, body, s2: String 
    --           args = joinBy " " $ toList f.args
    --           body = assert_total showU 5 f.body
    --           s2 = assert_total showU 4 n2
    --         --   ty: String
    --         --   ty = if forceTyVar then ": " ++ show f.ty else ""
    -- showPrec d (LetTuple xs n1 n2) = showParens (forceParen || d > User 4) "let (\{xs'})\{ts'} = \{s1} in \{s2}"
    --     where xs', ts', s1, s2: String 
    --           xs' = joinBy ", " $ toList xs
    --           ts' = ""
    --           s1 = assert_total showU 5 n1
    --           s2 = assert_total showU 4 n2
    --         --   ts' = if forceTyVar then ": " ++ (joinBy " * " $ show <$> toList ts) else ""

    show x = show $ (the (Doc ()) (assert_total pretty x))

doc: Doc ()
doc = "list" <+> align (encloseSep lbracket rbracket comma (map pretty [1,20,300,4000]))

-- public export
-- data IsNot : Node a -> Type where 
--     ItIsNot: {key: a} -> IsNot (Var {key} "not")

-- public export 
-- data IsArrayCreate: Node a -> Type where 
--     ItIsArrayCreate: {key: a} -> IsArrayCreate (Var {key} "Array.create")
--     ItIsArrayMake: {key: a} -> IsArrayCreate (Var {key} "Array.make")

-- public export 
-- data IsGet: Node a -> Type where 
--     ItIsGet: {key: a} -> IsGet (Get {key} n1 n2)

-- isNot: (n: Node a) -> Dec (IsNot n)
-- isNot n@(Var "not") = Yes ItIsNot
-- isNot _ = No $ believe_me

-- isArrayCreate: (n: Node a) -> Dec (IsArrayCreate n)
-- isArrayCreate n@(Var "Array.create") = Yes ItIsArrayCreate
-- isArrayCreate n@(Var "Array.make") = Yes ItIsArrayMake
-- isArrayCreate _ = No $ believe_me

-- isGet: (n: Node a) -> Dec (IsGet n)
-- isGet n@(Get _ _) = Yes ItIsGet
-- isGet _ = No $ believe_me

-- mutual
--     public export 
--     data WellFormedFunctionDef: FunDef a nArgs -> Type where
--         WellFormedFunDef: WellFormed body -> WellFormedFunctionDef (MkFunDef name args body)

--     public export
--     data WellFormed: Node a -> Type where 
--         WellFormedU: {key: a} -> WellFormed (U {key})
--         WellFormedI: {key: a} -> WellFormed (I {key} _)
--         WellFormedB: {key: a} -> WellFormed (B {key} _)
--         WellFormedF: {key: a} -> WellFormed (F {key} _)
--         WellFormedVar: {key: a} -> (x: String) -> WellFormed (Var {key} x)
--         WellFormedGet: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Get {key} n1 n2)
--         WellFormedNeg: {key: a} -> WellFormed n -> WellFormed (Neg {key} n)
--         WellFormedFNeg: {key: a} -> WellFormed n -> WellFormed (FNeg {key} n)
--         WellFormedNot: {key: a} -> WellFormed n1 -> {auto p: IsNot n1} -> WellFormed n2 -> WellFormed (App {key} n1 [n2])
--         WellFormedArray: {key: a} -> WellFormed n1 -> {auto p: IsArrayCreate n1} -> WellFormed n2 -> WellFormed n3 -> WellFormed (App {key} n1 [n2, n3])
--         -- WellFormedApp1: {key: a} -> WellFormed n1 -> {auto p: Not (IsNot n1)} -> {auto p': Not (IsArrayCreate n1)} -> WellFormed n2 -> WellFormed (App {key} n1 [n2])
--         WellFormedApp: {key: a} -> WellFormed n1 -> 
--             {auto p: Not (IsNot n1)} -> {auto p': Not (IsArrayCreate n1)} -> (nps: Vect (S n) (node: Node a ** WellFormed node)) -> WellFormed (App {key} n1 ((.fst) <$> nps)) -- `fst` does not work, but `(.fst)` does!!!
--         WellFormedFMul: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (FMul {key} n1 n2)
--         WellFormedFDiv: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (FDiv {key} n1 n2)
--         WellFormedFAdd: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (FAdd {key} n1 n2)
--         WellFormedFSub: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (FSub {key} n1 n2)
--         WellFormedAdd: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Add {key} n1 n2)
--         WellFormedSub: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Sub {key} n1 n2)
--         WellFormedEq: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Eq {key} n1 n2)
--         WellFormedNeq: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Neq {key} n1 n2)
--         WellFormedLt: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Lt {key} n1 n2)
--         WellFormedLe: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Le {key} n1 n2)
--         WellFormedGt: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Gt {key} n1 n2)
--         WellFormedGe: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Ge {key} n1 n2)
--         -- WellFormedTuple2: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Tuple {key} {n=0} [n1, n2])
--         WellFormedTuple: {key: a} -> {n: Nat} -> (nps: Vect (S (S n)) (node: Node a ** WellFormed node)) -> WellFormed (Tuple {key} {n} (DPair.fst <$> nps))
--         WellFormedPut: {key: a} -> WellFormed n1 -> {auto p: IsGet n1} -> WellFormed n2 -> WellFormed (Put {key} n1 n2)
--         WellFormedIf: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed n3 -> WellFormed (If {key} n1 n2 n3)
--         WellFormedSemi: {key: a} -> WellFormed n1 -> WellFormed n2 -> WellFormed (Semi {key} n1 n2)
--         WellFormedLet: {key: a} -> String -> WellFormed n1 -> WellFormed n2 -> WellFormed (Let {key} x n1 n2)
--         WellFormedLetRec: {key: a} -> WellFormedFunctionDef f -> WellFormed n2 -> WellFormed (LetRec {key} f n2)
--         WellFormedLetTuple: {key: a} -> Vect (2 + n) String -> WellFormed n1 -> WellFormed n2 -> WellFormed (LetTuple {key} xs n1 n2)

-- notIsWellFormed: IsNot n -> WellFormed n 
-- notIsWellFormed ItIsNot = WellFormedVar "not"

-- arrayCreateIsWellFormed: IsArrayCreate n -> WellFormed n
-- arrayCreateIsWellFormed ItIsArrayCreate = WellFormedVar "Array.create"
-- arrayCreateIsWellFormed ItIsArrayMake = WellFormedVar "Array.make"

-- lemma: IsNot n -> IsArrayCreate n -> Void
-- lemma ItIsNot ItIsArrayCreate impossible

-- lemma2: (np: (node: Node a ** WellFormed node)) -> WellFormed (fst np)
-- lemma2 (n ** w) = w

-- -- data Lemma3: Type -> Type where 
-- --     MkLemma3: (np: (n: Node a ** WellFormed n)) -> (n = fst np) -> Lemma3 (WellFormed n = WellFormed (fst np))


-- arrayCreateNeedsAtLeastTwoArgs: {key: a} -> IsArrayCreate n1 -> WellFormed (App {key} n1 [n2]) -> Void
-- arrayCreateNeedsAtLeastTwoArgs ItIsArrayCreate w with (w)
--     arrayCreateNeedsAtLeastTwoArgs ItIsArrayCreate w | WellFormedApp _ [_] {p'} = p' ItIsArrayCreate
-- arrayCreateNeedsAtLeastTwoArgs ItIsArrayMake w with (w)
--     arrayCreateNeedsAtLeastTwoArgs ItIsArrayMake w | (WellFormedApp _ [_] {p'}) = p' ItIsArrayMake

-- arrayCreateNeedsAtMostTwoArgs: {key: a} -> IsArrayCreate n1 -> (WellFormed (App {key} n1 (n2::n3::n4::ns'))) -> Void
-- arrayCreateNeedsAtMostTwoArgs ItIsArrayCreate w with (w)
--     arrayCreateNeedsAtMostTwoArgs ItIsArrayCreate w | (WellFormedApp _ (_::_::_::_) {p'}) = p' ItIsArrayCreate
-- arrayCreateNeedsAtMostTwoArgs ItIsArrayMake w with (w)
--     arrayCreateNeedsAtMostTwoArgs ItIsArrayMake w | (WellFormedApp _ (_::_::_::_) {p'}) = p' ItIsArrayMake

-- notNeedsOneArgument: {key: a} -> IsNot n1 -> WellFormed (App {key} n1 (n2::n3::ns)) -> Void
-- notNeedsOneArgument ItIsNot w with (w) 
--     notNeedsOneArgument ItIsNot w | (WellFormedApp _ (_::_::_) {p}) = p ItIsNot

-- putLhsMustBeGet: {key: a} -> Not (IsGet n1) -> WellFormed (Put {key} n1 n2) -> Void
-- putLhsMustBeGet contra (WellFormedPut _ _ {p}) = contra p

-- mutual
--     checkWellFormeds: {n: Nat} -> (ns: Vect n (Node a)) -> (res: Vect n (node: Node a ** Dec (WellFormed node)) ** ns = (.fst) <$> res) -- `fst` does not work, but (.fst) does
--     checkWellFormeds {n=0} [] = ([] ** Refl)
--     checkWellFormeds {n=S n'} (n1::ns) with (checkWellFormed n1) | (checkWellFormeds ns)
--         checkWellFormeds {n=S n'} (n1::ns) | p1 | (res ** pres) = ((n1 ** p1) :: res ** cong2 (::) Refl pres) 

--     checkNotWellFormed: {key: a} -> {n: Nat} -> (n1: Node a) -> {auto p: IsNot n1} -> (ns: Vect (1 + n) (Node a)) -> Dec (WellFormed (App {key} n1 ns))
--     checkNotWellFormed {key} n1 {p} [n2] with (checkWellFormed n2)
--         checkNotWellFormed {key} n1 {p} [n2] | Yes p2 = Yes $ WellFormedNot (notIsWellFormed p) {p} p2
--         checkNotWellFormed {key} n1 {p} [n2] | No b2 = No $ \w => case w of (WellFormedApp p1 [(_ ** p2)]) => b2 p2; (WellFormedNot p1 p2) => b2 p2
--     checkNotWellFormed {key} n1 {p} (n2::n3::_) = No (notNeedsOneArgument p)
--         -- checkNotWellFormed {key} n1 {p} (n2::n3::_) | No b2 | _ = No $ \w => case w of (WellFormedApp {p=p''} _ (_::_::_)) => p'' p; (WellFormedArray {p=p''} _ _ _) => lemma p p''
--         -- checkNotWellFormed {key} n1 {p} (n2::n3::_) | _ | No b3 = No $ \w => case w of (WellFormedApp {p=p''} _ (_::_::_)) => p'' p; (WellFormedArray {p=p''} _ _ p3) => b3 p3
    
--     checkArrayCreateWellFormed: {key: a} -> {n: Nat} -> (n1: Node a) -> {auto p: IsArrayCreate n1} -> (ns: Vect (1 + n) (Node a)) -> Dec (WellFormed (App {key} n1 ns))
--     checkArrayCreateWellFormed n1 ns with (checkWellFormeds ns)
--         checkArrayCreateWellFormed n1 [_] | ([_] ** _) = No $ arrayCreateNeedsAtLeastTwoArgs p
--         -- checkArrayCreateWellFormed n1 [_] | ([(_ ** No b2)] ** _) = No $ (\w => case w of (WellFormedApp1 _ p2) => b2 p2; (WellFormedNot _ p2) => b2 p2)
--         checkArrayCreateWellFormed n1 [n2, n3] | ([(n2' ** Yes p2), (n3' ** Yes p3)] ** prf) = Yes $ rewrite prf in WellFormedArray (arrayCreateIsWellFormed p) {p} p2 p3
--         checkArrayCreateWellFormed n1 [n2, n3] | (((n2' ** No b2)::_::_) ** prf) = No $ \w => case w of (WellFormedApp {p'} _ [_, _]) => p' p; (WellFormedArray _ p2 _) => case biinj (::) prf of prf' => b2 (rewrite sym $ fst prf' in p2)
--         checkArrayCreateWellFormed n1 [n2, n3] | ((_::(n3' ** No b3)::_) ** prf) = No $ \w => case w of (WellFormedApp {p'} _ [_, _]) => p' p; (WellFormedArray _ _ p3) => case biinj (::) prf of prf' => case biinj (::) (snd prf') of prf'' => b3 (rewrite sym $ fst prf'' in p3)
--         checkArrayCreateWellFormed n1 (n2::n3::n4::_) | _ = No $ arrayCreateNeedsAtMostTwoArgs p
    
--     checkAppWellFormed: {key: a} -> {n: Nat} -> (n1: Node a) -> {auto p: Not (IsNot n1)} -> {auto p': Not (IsArrayCreate n1)} -> (ns: Vect (1 + n) (Node a)) -> Dec (WellFormed (App {key} n1 ns))
--     checkAppWellFormed {key} n1 [n2] with (checkWellFormed n1) | (checkWellFormed n2)
--         checkAppWellFormed {key} n1 [n2] | Yes p1 | Yes p2 = Yes $ WellFormedApp p1 [(n2 ** p2)]
--         checkAppWellFormed {key} n1 [n2] | No a1 | _ = No $ \w => case w of (WellFormedApp p1 [_]) => a1 p1; (WellFormedNot p1 _) => a1 p1
--         checkAppWellFormed {key} n1 [n2] |  _ | No b2 = No $ \w => case w of (WellFormedApp _ [(_ **p2)]) => b2 p2; (WellFormedNot _ p2) => b2 p2
--     checkAppWellFormed {key} {n=S n'} {p'} n1 (n2::ns) with (checkWellFormed n2) | (checkAppWellFormed {key} {n=n'} n1 ns)
--         checkAppWellFormed {key} {n=S n'} {p'} n1 (n2::ns) | Yes p2 | Yes p1 = case p1 of (WellFormedApp p1' nps) => Yes $ WellFormedApp {p} {p'} p1' ((n2 ** p2) :: nps); (WellFormedArray {p=p''} _ _ _) => No $ (\_ => p' p''); (WellFormedNot {p=p''} _ _) => No $ (\_ => p p'')
--         checkAppWellFormed {key} {n=S n'} {p'} n1 (n2::ns) | No b2 | _ = No $ \w => case w of (WellFormedApp _ ((n2' ** p2)::_)) => b2 p2; (WellFormedArray {p=p''} _ _ _) => p' p''
--         checkAppWellFormed {key} {n=S n'} {p'} n1 (n2::ns) | _ | No b1 = No $ \w => case w of (WellFormedApp n1' (_::nps)) => b1 ((WellFormedApp {p} {p'} n1' nps)); (WellFormedArray {p=p''} _ _ _) => p' p''

--     checkBinaryWellFormed:
--     (n1: Node a) -> (n2: Node a) ->
--     (f:  Node a -> Node a -> Node a) -> 
--     (f': WellFormed n1 -> WellFormed n2 -> (WellFormed (f n1 n2))) -> 
--     (h1: (WellFormed n1 -> Void) -> WellFormed (f n1 n2) -> Void) -> 
--     (h2: (WellFormed n2 -> Void) -> WellFormed (f n1 n2) -> Void) -> Dec (WellFormed (f n1 n2))
--     checkBinaryWellFormed n1 n2 f f' h1 h2 with (checkWellFormed n1) | (checkWellFormed n2) 
--         checkBinaryWellFormed n1 n2 f f' h1 h2 | Yes p1 | Yes p2 = Yes $ f' p1 p2
--         checkBinaryWellFormed n1 n2 f f' h1 h2 | No a1 | _ = No $ h1 a1
--         checkBinaryWellFormed n1 n2 f f' h1 h2 | _ | No b2 = No $ h2 b2

--     export
--     checkWellFormed: (n: Node a) -> Dec (WellFormed n)
--     checkWellFormed U = Yes WellFormedU
--     checkWellFormed (I {key} _) = Yes (WellFormedI {key})
--     checkWellFormed (B _) = Yes WellFormedB
--     checkWellFormed (F _) = Yes WellFormedF
--     checkWellFormed (Var x) = Yes (WellFormedVar x)
--     checkWellFormed (Get n1 n2) = checkBinaryWellFormed n1 n2 Get WellFormedGet (\a, (WellFormedGet p1 _) => a p1) (\b, (WellFormedGet _ p2) => b p2)
--     checkWellFormed (Neg n) with (checkWellFormed n)
--         checkWellFormed (Neg n) | Yes p = Yes $ WellFormedNeg p
--         checkWellFormed (Neg n) | No contra = No $ \(WellFormedNeg p) => contra p
--     checkWellFormed (FNeg n) with (checkWellFormed n)
--         checkWellFormed (FNeg n) | Yes p = Yes $ WellFormedFNeg p
--         checkWellFormed (FNeg n) | No contra = No $ \(WellFormedFNeg p) => contra p
--     checkWellFormed (App {key} n1 ns) with (isNot n1) | (isArrayCreate n1)
--         checkWellFormed (App {key} n1 ns) | Yes p1 | Yes p2 = No (\_ => lemma p1 p2)
--         checkWellFormed (App {key} n1 ns) | Yes p1 | No _ = checkNotWellFormed n1 ns
--         checkWellFormed (App {key} n1 ns) | No _ | Yes p2 = checkArrayCreateWellFormed n1 ns
--         checkWellFormed (App {key} n1 ns) | No _ | No _ = checkAppWellFormed n1 ns
--     checkWellFormed (FMul n1 n2) = checkBinaryWellFormed n1 n2 FMul WellFormedFMul (\a, (WellFormedFMul p1 _) => a p1) (\b, (WellFormedFMul _ p2) => b p2)
--     checkWellFormed (FDiv n1 n2) = checkBinaryWellFormed n1 n2 FDiv WellFormedFDiv (\a, (WellFormedFDiv p1 _) => a p1) (\b, (WellFormedFDiv _ p2) => b p2)
--     checkWellFormed (FAdd n1 n2) = checkBinaryWellFormed n1 n2 FAdd WellFormedFAdd (\a, (WellFormedFAdd p1 _) => a p1) (\b, (WellFormedFAdd _ p2) => b p2)
--     checkWellFormed (FSub n1 n2) = checkBinaryWellFormed n1 n2 FSub WellFormedFSub (\a, (WellFormedFSub p1 _) => a p1) (\b, (WellFormedFSub _ p2) => b p2)
--     checkWellFormed (Add n1 n2) = checkBinaryWellFormed n1 n2 Add WellFormedAdd (\a, (WellFormedAdd p1 _) => a p1) (\b, (WellFormedAdd _ p2) => b p2)
--     checkWellFormed (Sub n1 n2) = checkBinaryWellFormed n1 n2 Sub WellFormedSub (\a, (WellFormedSub p1 _) => a p1) (\b, (WellFormedSub _ p2) => b p2)
--     checkWellFormed (Eq n1 n2) = checkBinaryWellFormed n1 n2 Eq WellFormedEq (\a, (WellFormedEq p1 _) => a p1) (\b, (WellFormedEq _ p2) => b p2)
--     checkWellFormed (Neq n1 n2) = checkBinaryWellFormed n1 n2 Neq WellFormedNeq (\a, (WellFormedNeq p1 _) => a p1) (\b, (WellFormedNeq _ p2) => b p2)
--     checkWellFormed (Lt n1 n2) = checkBinaryWellFormed n1 n2 Lt WellFormedLt (\a, (WellFormedLt p1 _) => a p1) (\b, (WellFormedLt _ p2) => b p2)
--     checkWellFormed (Le n1 n2) = checkBinaryWellFormed n1 n2 Le WellFormedLe (\a, (WellFormedLe p1 _) => a p1) (\b, (WellFormedLe _ p2) => b p2)
--     checkWellFormed (Gt n1 n2) = checkBinaryWellFormed n1 n2 Gt WellFormedGt (\a, (WellFormedGt p1 _) => a p1) (\b, (WellFormedGt _ p2) => b p2)
--     checkWellFormed (Ge n1 n2) = checkBinaryWellFormed n1 n2 Ge WellFormedGe (\a, (WellFormedGe p1 _) => a p1) (\b, (WellFormedGe _ p2) => b p2)
--     checkWellFormed (Tuple {key} [n1, n2]) with (checkWellFormed n1) | (checkWellFormed n2)
--         checkWellFormed (Tuple {key} [n1, n2]) | Yes p1 | Yes p2 = Yes $ WellFormedTuple {key} [(n1 ** p1), (n2 ** p2)]
--         checkWellFormed (Tuple {key} [n1, n2]) | No contra | _ = No $ \(WellFormedTuple [(_ ** p1), _]) => contra p1
--         checkWellFormed (Tuple {key} [n1, n2]) | _ | No b = No $ \(WellFormedTuple [_, (_ **p2)]) => b p2
--     checkWellFormed (Tuple {key} (n1::n2::n3::ns)) with (checkWellFormed n1) | (checkWellFormed (Tuple {key} (n2::n3::ns)))
--         checkWellFormed (Tuple {key} (n1::n2::n3::ns)) | Yes p1 | Yes p2 = Yes $ case p2 of (WellFormedTuple ((_ ** p2')::(_ ** p3')::nps)) => WellFormedTuple {key} ((n1 ** p1) :: (n2 ** p2') :: (n3 ** p3') :: nps)
--         checkWellFormed (Tuple {key} (n1::n2::n3::ns)) | No contra | _ = No $ \(WellFormedTuple ((_ ** p1)::_::_::_)) => contra p1
--         checkWellFormed (Tuple {key} (n1::n2::n3::ns)) | _ | No b = No $ \(WellFormedTuple (_::np2::np3::nps)) => b (WellFormedTuple {key} (np2::np3::nps))
--     checkWellFormed (Put {key} n1 n2) with (checkWellFormed n1) | (checkWellFormed n2)
--         checkWellFormed (Put {key} n1 n2) | No contra | _ = No $ \(WellFormedPut p1 _) => contra p1
--         checkWellFormed (Put {key} n1 n2) | _ | No b = No $ \(WellFormedPut _ p2) => b p2
--         checkWellFormed (Put {key} n1 n2) | Yes p1 | Yes p2 with (isGet n1)
--             checkWellFormed (Put {key} n1 n2) | Yes p1 | Yes p2 | Yes _ = Yes $ WellFormedPut {key} p1 p2
--             checkWellFormed (Put {key} n1 n2) | Yes p1 | Yes p2 | No g = No $ putLhsMustBeGet g
--     checkWellFormed (If {key} n1 n2 n3) with (checkWellFormed n1) | (checkWellFormed n2) 
--         checkWellFormed (If {key} n1 n2 n3) | No contra | _ = No $ \(WellFormedIf p1 _ _) => contra p1
--         checkWellFormed (If {key} n1 n2 n3) | _ | No b = No $ \(WellFormedIf _ p2 _) => b p2
--         checkWellFormed (If {key} n1 n2 n3) | Yes p1 | Yes p2 with (checkWellFormed n3)
--             checkWellFormed (If {key} n1 n2 n3) | Yes p1 | Yes p2 | Yes p3 = Yes $ WellFormedIf {key} p1 p2 p3
--             checkWellFormed (If {key} n1 n2 n3) | Yes p1 | Yes p2 | No c = No $ \(WellFormedIf _ _ p3) => c p3
--     checkWellFormed (Semi {key} n1 n2) = checkBinaryWellFormed n1 n2 Semi WellFormedSemi (\a, (WellFormedSemi p1 _) => a p1) (\b, (WellFormedSemi _ p2) => b p2)
--     checkWellFormed (Let {key} x n1 n2) with (checkWellFormed n1) | (checkWellFormed n2)
--         checkWellFormed (Let {key} x n1 n2) | Yes p1 | Yes p2 = Yes $ WellFormedLet {key} x p1 p2
--         checkWellFormed (Let {key} x n1 n2) | No contra | _ = No $ \(WellFormedLet _ p1 _) => contra p1
--         checkWellFormed (Let {key} x n1 n2) | _ | No b = No $ \(WellFormedLet _ _ p2) => b p2
--     checkWellFormed (LetRec {key} (MkFunDef _ _ body) n2) with (checkWellFormed body) | (checkWellFormed n2)
--         checkWellFormed (LetRec {key} (MkFunDef _ _ body) n2) | Yes body' | Yes p2 = Yes $ WellFormedLetRec {key} (WellFormedFunDef body') p2
--         checkWellFormed (LetRec {key} (MkFunDef _ _ body) n2) | _ | No contra = No $ \(WellFormedLetRec _ p2) => contra p2
--         checkWellFormed (LetRec {key} (MkFunDef _ _ body) n2) | No b | _ = No $ \(WellFormedLetRec (WellFormedFunDef body') _) => b body'
--     checkWellFormed (LetTuple {key} xs n1 n2) with (checkWellFormed n1) | (checkWellFormed n2)
--         checkWellFormed (LetTuple {key} xs n1 n2) | Yes p1 | Yes p2 = Yes $ WellFormedLetTuple {key} xs p1 p2
--         checkWellFormed (LetTuple {key} xs n1 n2) | No contra | _ = No $ \(WellFormedLetTuple _ p1 _) => contra p1
--         checkWellFormed (LetTuple {key} xs n1 n2) | _ | No b = No $ \(WellFormedLetTuple _ _ p2) => b p2

-- mutual
--     public export
--     data FunDefIsTyped: (f: FunDef a (1 + nArgs')) -> Ty -> Type where
--         MkFunDefIsTyped: (argsTy: Vect (1 + nArgs') Ty) -> IsTyped body retTy -> FunDefIsTyped (MkFunDef name args body) (TyFun argsTy retTy)

--     public export
--     data IsTyped: Node a -> Ty -> Type where
--         TypedU: {key: a} -> IsTyped (U {key}) TyUnit
--         TypedI: {key: a} -> IsTyped (I _ {key}) TyI32
--         TypedB: {key: a} -> IsTyped (B _ {key}) TyBool
--         TypedF: {key: a} -> IsTyped (F _ {key}) TyF32
--         TypedVar: {key: a} -> String -> Ty -> IsTyped (Var {key} x) t
--         TypedGet: {key: a} -> IsTyped n1 (TyArray t) -> IsTyped n2 TyI32 -> IsTyped (Get {key} n1 n2) t
--         TypedNeg: {key: a} -> IsTyped n TyI32 -> IsTyped (Neg {key} n) TyI32
--         TypedFNeg: {key: a} -> IsTyped n TyF32 -> IsTyped (FNeg {key} n) TyF32
--         -- TypedNot: {key: a} -> IsTyped n1 b -> {auto p: IsNot n1} -> IsTyped n2 TyBool -> IsTyped (App {key} n1 [n2]) TyBool
--         -- TypedArray: {key: a} -> IsTyped n1 TyI32 -> {auto p: IsArrayCreate n1} -> IsTyped n2 t -> IsTyped (n3) (TyArray t) -> IsTyped (App {key} n1 [n2, n3]) (TyArray t)
--         TypedApp: {key: a} ->  {-{auto p: Not (IsNot n1)} -> {auto p': Not (IsArrayCreate n1)} -} 
--         (args: Vect (S nargs') (DPair (Node a, Ty) (uncurry IsTyped))) -> IsTyped n1 (TyFun (Builtin.snd <$> DPair.fst <$> args) retTy) -> 
--         IsTyped ((App {key} n1 (Builtin.fst <$> DPair.fst <$> args))) retTy

--         TypedFMul: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FMul {key} n1 n2) TyF32
--         TypedFDiv: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FDiv {key} n1 n2) TyF32
--         TypedFAdd: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FAdd {key} n1 n2) TyF32
--         TypedFSub: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FSub {key} n1 n2) TyF32
--         TypedAdd: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Add {key} n1 n2) TyI32
--         TypedSub: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Sub {key} n1 n2) TyI32
--         TypedEqi: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Eq {key} n1 n2) TyBool
--         TypedEqb: {key: a} -> IsTyped n1 TyBool -> IsTyped n2 TyBool -> IsTyped (Eq {key} n1 n2) TyBool
--         TypedEqf: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Eq {key} n1 n2) TyBool
--         TypedNeqi: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Neq {key} n1 n2) TyBool
--         TypedNeqb: {key: a} -> IsTyped n1 TyBool -> IsTyped n2 TyBool -> IsTyped (Neq {key} n1 n2) TyBool
--         TypedNeqf: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Neq {key} n1 n2) TyBool
--         TypedLti: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Lt {key} n1 n2) TyBool
--         TypedLtf: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Lt {key} n1 n2) TyBool
--         TypedLei: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Le {key} n1 n2) TyBool
--         TypedLef: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Le {key} n1 n2) TyBool
--         TypedGti: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Gt {key} n1 n2) TyBool
--         TypedGtf: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Gt {key} n1 n2) TyBool
--         TypedGei: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Ge {key} n1 n2) TyBool
--         TypedGef: {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Ge {key} n1 n2) TyBool
--         -- TypedTuple2: {key: a} -> IsTyped n1 t1 -> IsTyped n2 t2 -> IsTyped (Tuple {key} {n=0} [n1, n2]) (TyTuple [t1, t2])
--         TypedTuple: {key: a} -> {n: Nat} -> (ns: Vect (S (S n)) (DPair (Node a, Ty) (uncurry IsTyped))) -> IsTyped (Tuple {key} {n} (Builtin.fst <$> DPair.fst <$> ns)) (TyTuple (Builtin.snd <$> DPair.fst <$> ns))
--         TypedPut: {key: a} -> IsTyped n1 (TyArray t) -> IsTyped n2 TyI32 -> IsTyped n3 t -> IsTyped (Put {key} n1 n2 n3) t
--         TypedIf: {key: a} -> IsTyped n1 TyBool -> IsTyped n2 t -> IsTyped (n3) t -> IsTyped (If {key} n1 n2 n3) t
--         TypedSemi: {key: a} -> IsTyped n1 TyUnit -> IsTyped n2 t -> IsTyped (Semi {key} n1 n2) t
--         TypedLet: {key: a} -> String -> IsTyped n1 t1 -> IsTyped n2 t2 -> IsTyped (Let {key} x n1 n2) t2
--         TypedLetRec: {key: a} -> FunDefIsTyped (f) ft -> IsTyped n2 t2 -> IsTyped (LetRec {key} f n2) t2
--         TypedLetTuple: {key: a} -> Vect (2 + n) String -> (ts: Vect (2 + n) Ty) -> IsTyped n1 (TyTuple ts) -> IsTyped n2 t2 -> IsTyped (LetTuple {key} xs n1 n2) t2
        -- TypedArray: {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 t -> IsTyped (Array {key} n1 n2) (TyArray t)

-- mutual 
--     checkTypeds: {env: List (String, Ty)} -> (ns: Vect n (Node a)) -> Either String (ntps: Vect n (DPair (Node a, Ty) (uncurry IsTyped)) ** ns = Builtin.fst <$> DPair.fst <$> ntps)
--     checkTypeds [] = pure ([] ** Refl)
--     checkTypeds {env} (n::ns) with (checkTyped {env} n) | (checkTypeds {env} ns)
--         checkTypeds (n::ns) | Right (t ** p) | Right (ts ** prf) = pure (((n, t) ** p) :: ts ** cong2 (::) Refl prf)
--         checkTypeds (n::ns) | Right (t ** p) | Left err = Left err
--         checkTypeds (n::ns) | Left err | _ = Left err
    
--     checkTyped: {env: List (String, Ty)} -> (n: Node a) -> Either String (t: Ty ** IsTyped n t)
--     checkTyped U = pure (TyUnit ** TypedU)
--     -- checkTyped U t = Left "unit is not of type \{show t}"
--     checkTyped (I _ {key}) = pure (TyI32 ** TypedI)
--     -- checkTyped (I _ {key}) t = Left "int is not of type \{show t}"
--     checkTyped (B _ {key}) = pure (TyBool ** TypedB)
--     -- checkTyped (B _ {key}) t = Left "bool is not of type \{show t}"
--     checkTyped (F _ {key}) = pure (TyF32 ** TypedF)
--     -- checkTyped (F _ {key}) t = Left "float is not of type \{show t}"
--     checkTyped (Var x {key}) = case lookup x env of
--         Just t => pure (t ** TypedVar x t)
--         Nothing => Left $ "variable \{x} not found"
--     checkTyped {env} (Get {key} n1 n2) with (checkTyped {env} n1) | (checkTyped {env} n2)
--         checkTyped (Get {key} n1 n2) | Right (TyArray t ** p1) | Right (TyI32 ** p2) = pure (t ** TypedGet p1 p2)
--         checkTyped (Get {key} n1 n2) | Right (TyArray t ** _) | Right (i ** _) = Left $ "expect \{show n2} to be of type \{show TyI32}, but got \{show i}"
--         checkTyped (Get {key} n1 n2) | Right (t ** _) | Right (TyI32 ** _) = Left $ "expect \{show n1} to be of type \{show (TyArray t)}, but got \{show t}"
--         checkTyped (Get {key} n1 n2) | Right (t ** _) | Right (i ** _) = Left $ "expect \{show n1} to be of type \{show (TyArray t)}, but got \{show t} and \{show n2} to be of type \{show TyI32}, but got \{show i}"
--         checkTyped (Get {key} n1 n2) | Left err | _ = Left err
--         checkTyped (Get {key} n1 n2) | _ | Left err = Left err
--     checkTyped {env} (Neg {key} n) with (checkTyped {env} n)
--         checkTyped (Neg {key} n) | Right (TyI32 ** p) = pure (TyI32 ** TypedNeg p)
--         checkTyped (Neg {key} n) | Right (t ** _) = Left $ "expect \{show n} to be of type \{show TyI32}, but got \{show t}"
--         checkTyped (Neg {key} n) | Left err = Left err
--     checkTyped {env} (FNeg {key} n) with (checkTyped {env} n)
--         checkTyped (FNeg {key} n) | Right (TyF32 ** p) = pure (TyF32 ** TypedFNeg p)
--         checkTyped (FNeg {key} n) | Right (t ** _) = Left $ "expect \{show n} to be of type \{show TyF32}, but got \{show t}"
--         checkTyped (FNeg {key} n) | Left err = Left err
--     checkTyped (App {n} {key} n1 ns) with (checkTyped {env} n1) | (checkTypeds {env} ns)
--         checkTyped (App {key} n1 ns) | Right (TyFun {n=n'} ts retTy ** p1) | Right (ntps ** prf) with (decEq n n') 
--             checkTyped (App {key} n1 ns) | Right (TyFun {n=n'} ts retTy ** p1) | Right (ntps ** prf) | Yes nEqn' with (decEq (rewrite nEqn' in ts) (snd <$> fst <$> ntps))
--                 checkTyped (App {key} n1 ns) | Right (TyFun ts retTy ** p1) | Right (ntps ** prf) | Yes nEqn' | Yes p = ?hh *> pure (retTy ** rewrite prf in TypedApp ntps (rewrite sym p in rewrite nEqn' in p1))
--                 checkTyped (App {key} n1 ns) | Right (TyFun ts retTy ** _) | Right (ntps ** prf) | Yes nEqn' | No contra = Left $ "expect \{show n2} to be of type \{show t}, but got \{show t'}"