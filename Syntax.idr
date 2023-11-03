module Syntax

import Data.Vect
import Data.String
import Text.Lexer
import Ty

public export
data NodeKeyType: Type where
    NodeKey: NodeKeyType

public export
interface Info a where
    key: a -> NodeKeyType
    -- bounds: a -> Bounds
export
Info Nat where 
    key _ = NodeKey
    
-- public export
-- Info Bounds where
--     key _ = NodeKey
--     bounds x = x
mutual
    public export
    record FunDef (nArgs: Nat) where
        constructor MkFunDef
        name: String
        ty: TypeVar
        args: Vect (1 + nArgs) String
        argsTy: Vect (1 + nArgs) TypeVar
        body: Node

    public export
    data Node: Type where
        U: (Info a) => {key: a} -> Node
        I: (Info a) => {key: a} -> Int -> Node
        B: (Info a) => {key: a} -> Bool -> Node
        F: (Info a) => {key: a} -> Double -> Node
        Var: (Info a) => {key: a} -> String -> Node

        Get: (Info a) => {key: a} -> Node -> Node -> Node

        Neg: (Info a) => {key: a} -> Node -> Node
        FNeg: (Info a) => {key: a} -> Node -> Node

        Not: (Info a) => {key: a} -> Node -> Node
        App: (Info a) => {key: a} -> Node -> TypeVar -> Vect (1 + n) Node -> TypeVar -> Node
        Array: (Info a) => {key: a} -> Node -> Node -> Node

        FMul: (Info a) => {key: a} -> Node -> Node -> Node
        FDiv: (Info a) => {key: a} -> Node -> Node -> Node

        FAdd: (Info a) => {key: a} -> Node -> Node -> Node
        FSub: (Info a) => {key: a} -> Node -> Node -> Node
        Add: (Info a) => {key: a} -> Node -> Node -> Node
        Sub: (Info a) => {key: a} -> Node -> Node -> Node

        Eq: (Info a) => {key: a} -> Node -> Node -> Node
        Neq: (Info a) => {key: a} -> Node -> Node -> Node
        Lt: (Info a) => {key: a} -> Node -> Node -> Node
        Le: (Info a) => {key: a} -> Node -> Node -> Node
        Gt: (Info a) => {key: a} -> Node -> Node -> Node
        Ge: (Info a) => {key: a} -> Node -> Node -> Node

        Tuple: (Info a) => {key: a} -> Vect (2 + n) Node -> Vect (2 + n) TypeVar -> Node

        Put: (Info a) => {key: a} -> Node -> Node -> Node

        If: (Info a) => {key: a} -> Node -> Node -> Node -> Node

        Semi: (Info a) => {key: a} -> Node -> Node -> Node

        Let: (Info a) => {key: a} -> String -> TypeVar -> Node -> Node -> Node
        LetRec: (Info a) => {key: a} -> {nArgs: Nat} -> FunDef nArgs -> Node -> Node
        LetTuple: (Info a) => {key: a} -> {n: Nat} -> Vect (2 + n) String -> Vect (2 + n) TypeVar -> Node -> Node -> Node
    
    export
    (.key): (Info a) => {key: a} -> Node -> a
    (.key) {key} _ = key

showU: Show a => Nat -> a -> String 
showU x = assert_total showPrec (User x)

forceParen: Bool 
forceParen = False
forceTyVar: Bool
forceTyVar = True

export
Show Node where 
    showPrec _ U = "()"
    showPrec _ (I i) = show i
    showPrec _ (B b) = if b then "true" else "false"
    showPrec _ (F f) = show f
    showPrec _ (Var x) = x

    showPrec _ (Get n1 n2) = "\{assert_total showU 24 n1}.(\{assert_total showU 0 n2})"

    showPrec d (Not n) = showParens (forceParen || d > User 22) "not \{assert_total showU 23 n}"
    showPrec d (App n1 _ n2s _) = showParens (forceParen || d > User 22) "\{assert_total showU 22 n1} \{joinBy " " $ toList $ assert_total showU 23 <$> n2s}"
    showPrec d (Array n1 n2) = showParens (forceParen || d > User 22) "Array.create \{assert_total showU 23 n1} \{assert_total showU 23 n2}"

    showPrec d (Neg n) = showParens (forceParen || d > User 20) "-\{assert_total showU 21 n}"
    showPrec d (FNeg n) = showParens (forceParen || d > User 20) "-.\{assert_total showU 21 n}"

    showPrec d (FMul n1 n2) = showParens (forceParen || d > User 18) "\{assert_total showU 18 n1} *. \{assert_total showU 18 n2}"
    showPrec d (FDiv n1 n2) = showParens (forceParen || d > User 18) "\{assert_total showU 18 n1} /. \{assert_total showU 19 n2}"

    showPrec d (FAdd n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} +. \{assert_total showU 16 n2}"
    showPrec d (FSub n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} -. \{assert_total showU 17 n2}"
    showPrec d (Add n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} + \{assert_total showU 16 n2}"
    showPrec d (Sub n1 n2) = showParens (forceParen || d > User 16) "\{assert_total showU 16 n1} - \{assert_total showU 17 n2}"

    showPrec d (Eq n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} = \{assert_total showU 15 n2}"
    showPrec d (Neq n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} <> \{assert_total showU 15 n2}"
    showPrec d (Lt n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} < \{assert_total showU 15 n2}"
    showPrec d (Le n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} <= \{assert_total showU 15 n2}"
    showPrec d (Gt n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} > \{assert_total showU 15 n2}"
    showPrec d (Ge n1 n2) = showParens (forceParen || d > User 14) "\{assert_total showU 15 n1} >= \{assert_total showU 15 n2}"

    showPrec d (Tuple ns ts) = 
        if forceTyVar then showParens True "(\{joinBy ", " $ toList $ assert_total showU 13 <$> ns}): (\{joinBy " * " $ toList $ assert_total showU 13 <$> ts})"
          else showParens True "\{joinBy ", " $ toList $ assert_total showU 13 <$> ns}"
    showPrec d (Put n1 n2) = showParens (forceParen || d > User 10) "\{assert_total showU 11 n1} <- \{assert_total showU 11 n2}"

    showPrec d (If n1 n2 n3) = showParens (forceParen || d > User 8) "if \{assert_total showU 9 n1} then \{assert_total showU 8 n2} else \{assert_total showU 8 n3}"

    showPrec d (Semi n1 n2) = showParens (forceParen || d > User 6) "\{assert_total showU 7 n1}; \{assert_total showU 6 n2}"

    showPrec d (Let x t n1 n2) = 
        if forceTyVar then 
            showParens (forceParen || d > User 4) "let \{x}: \{t} = \{assert_total showU 5 n1} in\n\{assert_total showU 4 n2}"
          else showParens (forceParen || d > User 4) "let \{x} = \{assert_total showU 5 n1} in\n\{assert_total showU 4 n2}" 

    showPrec d (LetRec f n2) = showParens (forceParen || d > User 4) "let rec \{f.name} \{args}\{ty} = \{assert_total showU 5 f.body} in\n\{assert_total showU 4 n2}" 
        where args : String 
              args = if forceTyVar then ": " ++ (joinBy " " $ toList $ zip f.args f.argsTy <&> (\(x, t) => "(\{x}: \{t})")) 
                        else " " ++ (joinBy " " $ toList f.args)
              ty: String
              ty = if forceTyVar then ": " ++ show f.ty else ""
    showPrec d (LetTuple xs ts n1 n2) = showParens (forceParen || d > User 4) "let (\{xs'})\{ts'} = \{assert_total showU 5 n1} in\n\{assert_total showU 4 n2}"
        where xs' : String 
              xs' = joinBy ", " $ toList xs
              ts' : String
              ts' = if forceTyVar then ": " ++ (joinBy " * " $ show <$> toList ts) else ""

    show x = assert_total showU 0 x

public export
data FunDefIsTyped: FunDef (1 + nArgs') -> Ty -> Type where
    MkFunDefIsTyped: (argsTy: Vect (1 + nArgs') Ty) -> (t: Ty) -> FunDefIsTyped (MkFunDef name tyvar args argsTyvar body) (TyFun {n=nArgs'} argsTy t)
public export
data IsTyped: Node -> Ty -> Type where
    TypedU: (Info a) => {key: a} -> IsTyped (U {key}) TyUnit
    TypedI: (Info a) => {key: a} -> IsTyped (I {key} _) TyI32
    TypedB: (Info a) => {key: a} -> IsTyped (B {key} _) TyBool
    TypedF: (Info a) => {key: a} -> IsTyped (F {key} _) TyF32
    TypedNot: (Info a) => {key: a} -> IsTyped n TyBool -> IsTyped (Not {key} n) TyBool
    TypedNeg: (Info a) => {key: a} -> IsTyped n TyI32 -> IsTyped (Neg {key} n) TyI32
    TypedAdd: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Add {key} n1 n2) TyI32
    TypedSub: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Sub {key} n1 n2) TyI32
    TypedFNeg: (Info a) => {key: a} -> IsTyped n TyF32 -> IsTyped (FNeg {key} n) TyF32
    TypedFAdd: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FAdd {key} n1 n2) TyF32
    TypedFSub: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FSub {key} n1 n2) TyF32
    TypedFMul: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FMul {key} n1 n2) TyF32
    TypedFDiv: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (FDiv {key} n1 n2) TyF32
    TypedEqi: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Eq {key} n1 n2) TyBool
    TypedEqb: (Info a) => {key: a} -> IsTyped n1 TyBool -> IsTyped n2 TyBool -> IsTyped (Eq {key} n1 n2) TyBool
    TypedEqf: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Eq {key} n1 n2) TyBool
    TypedNeqi: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Neq {key} n1 n2) TyBool
    TypedNeqb: (Info a) => {key: a} -> IsTyped n1 TyBool -> IsTyped n2 TyBool -> IsTyped (Neq {key} n1 n2) TyBool
    TypedNeqf: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Neq {key} n1 n2) TyBool
    TypedLti: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Lt {key} n1 n2) TyBool
    TypedLtf: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Lt {key} n1 n2) TyBool
    TypedLei: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Le {key} n1 n2) TyBool
    TypedLef: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Le {key} n1 n2) TyBool
    TypedGti: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Gt {key} n1 n2) TyBool
    TypedGtf: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Gt {key} n1 n2) TyBool
    TypedGei: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 TyI32 -> IsTyped (Ge {key} n1 n2) TyBool
    TypedGef: (Info a) => {key: a} -> IsTyped n1 TyF32 -> IsTyped n2 TyF32 -> IsTyped (Ge {key} n1 n2) TyBool
    TypedIf: (Info a) => {key: a} -> IsTyped n1 TyBool -> IsTyped n2 t -> IsTyped n3 t -> IsTyped (If {key} n1 n2 n3) t
    TypedVar: (Info a) => {key: a} -> String -> Ty -> IsTyped (Var {key} x) t
    TypedLet: (Info a) => {key: a} -> String -> TypeVar -> IsTyped n1 t1 -> IsTyped n2 t2 -> IsTyped (Let {key} x ty n1 n2) t2
    TypedLetRec: (Info a) => {key: a} -> FunDefIsTyped f ft -> IsTyped n2 t2 -> IsTyped (LetRec {key} f n2) t2
    TypedLetTuple: (Info a) => {key: a} -> Vect (2 + n) String -> (ts: Vect (2 + n) Ty) -> IsTyped n1 (TyTuple ts) -> IsTyped n2 t2 -> IsTyped (LetTuple {key} xs tys n1 n2) t2
    TypedPut: (Info a) => {key, key': a} -> IsTyped (Get {key=key'} n1 n2) t -> IsTyped n3 t -> IsTyped (Put {key} (Get {key=key'} n1 n2) n3) TyUnit
    TypedGet: (Info a) => {key: a} -> IsTyped n1 (TyArray t) -> IsTyped n2 TyI32 -> IsTyped (Get {key} n1 n2) t
    TypedArray: (Info a) => {key: a} -> IsTyped n1 TyI32 -> IsTyped n2 t -> IsTyped (Array {key} n1 n2) (TyArray t)
