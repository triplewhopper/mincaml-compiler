module KNormal

import Data.Vect
import Data.List
import Data.List1
import Data.Nat
import Data.Fun
import Data.String
import Data.Nat.Order
import Data.SortedSet as SortedSet
import Data.SortedMap as SortedMap
import Decidable.Equality
import Control.Monad.State
import Control.Monad.Either
import Control.Monad.Reader
import Syntax.WithProof
import Binding
import Info
import NonNullString
import Syntax
import Utils
import Text.Lexer


public export
0 Env: Type
Env = List Binding

In: (x: a) -> (xs: List a) -> Type
In x [] = Void
In x (y::ys) = (x = y) `Either` (In x ys)

public export 
revAppend: Vect n a -> List a -> List a 
revAppend [] ys = ys
revAppend (x::xs) ys = revAppend xs (x::ys)

public export
revAppendLemma: (xts: Vect n a) -> (ys: List a) -> length (revAppend xts ys) = length xts + length ys
revAppendLemma [] ys = Refl 
revAppendLemma (x::xs) ys = rewrite plusSuccRightSucc (length xs) (length ys) in revAppendLemma xs (x::ys)

mutual
    public export
    data KNormal: Type -> Env -> Type where
        U: {key: a} -> KNormal a env
        B: {key: a} -> Bool -> KNormal a env
        I: {key: a} -> Int -> KNormal a env
        Fl: {key: a} -> Double -> KNormal a env
        Var: {key: a} -> {env: Env} -> IdName Variable -> KNormal a env
        Get: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        Neg: {key: a} -> {env: Env} -> (x: Id) -> KNormal a env
        FNeg: {key: a} -> {env: Env} -> (x: Id) -> KNormal a env
        App: {key: a} -> {env: Env} -> (x: IdName Variable) -> {auto p: IsVarName x} -> {n: Nat} -> (args: Vect (1 + n) Id) -> KNormal a env
        AppTmp: {key: a} -> {env: Env} -> (x: IdName Temporary) -> {n: Nat} -> (args: Vect (1 + n) Id) -> KNormal a env
        ExtArray: {key: a} -> {env: Env} -> (x: NonNullString) -> KNormal a env
        ExtFunApp: {key: a} -> {env: Env} -> (x: NonNullString) -> {n: Nat} -> (Vect (1 + n) Id) -> KNormal a env
        FMul: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        FDiv: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        FAdd: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        FSub: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        Add: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        Sub: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env
        Tuple: {key: a} -> {env: Env} -> {n: Nat} -> (xs: Vect (2 + n) Id) -> KNormal a env
        Put: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> (z: Id) -> KNormal a env
        IfFalse: {key: a} -> {env: Env} -> (x: Id) -> KNormal a env -> KNormal a env -> KNormal a env
        IfEqi: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env -> KNormal a env -> KNormal a env
        IfLEi: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env -> KNormal a env -> KNormal a env
        IfEqf: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env -> KNormal a env -> KNormal a env
        IfLEf: {key: a} -> {env: Env} -> (x: Id) -> (y: Id) -> KNormal a env -> KNormal a env -> KNormal a env
        Let: {key: a} -> {env: Env} -> (x: IdName Variable) -> (t: Ty) -> (rhs: KNormal a env) -> KNormal a ((x, t)::env) -> KNormal a env
        LetTmp: {key: a} -> {env: Env} -> (x: IdName Temporary) -> (t: Ty) -> KNormal a env -> KNormal a env -> KNormal a env
        LetRec: {key: a} -> {env: Env} -> {arity': Nat} -> (f: FunDef a env arity') -> KNormal a (getName f :: env) -> KNormal a env
        LetTuple: {key: a} -> {env: Env}-> {k: Nat} -> (tup: Vect (2 + k) Binding) -> (y: Id) -> KNormal a (revAppend tup env) -> KNormal a env

    public export
    record FunDef (a: Type) (env: Env) (arity': Nat) where
        constructor MkFunDef
        name : Binding
        args : Vect (S arity') Binding      
        body : KNormal a (revAppend args (name::env))

    public export
    getName: FunDef a env arity -> Binding
    getName (MkFunDef name _ _) = name

    -- public export 
    -- data IsNotLet: KNormal a env -> Type where 
    --     UIsNotLet: IsNotLet (U {key})
    --     BIsNotLet: IsNotLet (B {key} _)
    --     IIsNotLet: IsNotLet (I {key} _)
    --     FlIsNotLet: IsNotLet (Fl {key} _)
    --     VarIsNotLet: IsNotLet (Var {key} _)
    --     GetIsNotLet: IsNotLet (Get {key} x y)
    --     NegIsNotLet: IsNotLet (Neg {key} x)
    --     FNegIsNotLet: IsNotLet (FNeg {key} x)
    --     AppIsNotLet: IsNotLet (App {key} x {p} args)
    --     AppTmpIsNotLet: IsNotLet (AppTmp {key} x args)
    --     ExtArrayIsNotLet: IsNotLet (ExtArray {key} x)
    --     ExtFunAppIsNotLet: IsNotLet (ExtFunApp {key} x args)
    --     FMulIsNotLet: IsNotLet (FMul {key} x y)
    --     FDivIsNotLet: IsNotLet (FDiv {key} x y)
    --     FAddIsNotLet: IsNotLet (FAdd {key} x y)
    --     FSubIsNotLet: IsNotLet (FSub {key} x y)
    --     AddIsNotLet: IsNotLet (Add {key} x y)
    --     SubIsNotLet: IsNotLet (Sub {key} x y)
    --     TupleIsNotLet: IsNotLet (Tuple {key} {n} xs)
    --     PutIsNotLet: IsNotLet (Put {key} x y z)
    --     IfFalseIsNotLet: IsNotLet (IfFalse {key} x e1 e2)
    --     IfEqiIsNotLet: IsNotLet (IfEqi {key} x y e1 e2)
    --     IfLEiIsNotLet: IsNotLet (IfLEi {key} x y e1 e2)
    --     IfEqfIsNotLet: IsNotLet (IfEqf {key} x y e1 e2)
    --     IfLEfIsNotLet: IsNotLet (IfLEf {key} x y e1 e2)




data InRange : Nat -> Nat -> Type where
    IsInRange : (x : Nat) -> (n <= x = True) -> (x <= m = True) -> InRange n m

shift: {x1, x2: IdName Variable} -> {t1, t2: Ty} -> 
(x1 = x2) -> (t1 = t2) -> KNormal a ((x1, t1)::env) -> KNormal a ((x2, t2)::env)
shift Refl Refl e = e

shiftWithArgs: {f1, f2: IdName Variable} -> {t1, t2: Ty} -> {args1, args2: Vect n Binding} ->
(f1 = f2) -> (t1 = t2) -> (args1 = args2) -> KNormal a (revAppend args1 ((f1, t1)::env)) -> KNormal a (revAppend args2 ((f2, t2)::env))
shiftWithArgs Refl Refl Refl e = e

eqVect: (Eq a) => {n, m: Nat} -> Vect n a -> Vect m a -> Bool 
eqVect xs ys with (decEq n m)
    eqVect xs ys | Yes nEqm = xs == (rewrite nEqm in ys)
    eqVect xs ys | No _ = False

mutual 
    Eq (FunDef a env arity) where
        MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 with (decEq f1 f2) | (assert_total decEq t1 t2)
            MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 with (assert_total decEq args1 args2)
                MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 | Yes args1Eqargs2 = assert_total (==) (shiftWithArgs f1Eqf2 t1Eqt2 args1Eqargs2 body1) body2
                MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 | No _ = {-if args1 == args2 then warn "fuck! 5" False else-} False
            MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | No _ | _ = {-if f1 == f2 then warn "fuck! 6" False else-} False 
            MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | _ | No _ = {-if t1 == t2 then warn "fuck! 7" False else-} False 
    export 
    Eq (KNormal a env) where 
        U == U = True
        B b1 == B b2 = b1 == b2
        I i1 == I i2 = i1 == i2
        Fl f1 == Fl f2 = f1 == f2
        Var x1 == Var x2 = x1 == x2
        Get x1 y1 == Get x2 y2 = x1 == x2 && y1 == y2
        Neg x1 == Neg x2 = x1 == x2
        FNeg x1 == FNeg x2 = x1 == x2
        App x1 xs1 == App x2 xs2 = x1 == x2 && eqVect xs1 xs2
        AppTmp x1 xs1 == AppTmp x2 xs2 = x1 == x2 && eqVect xs1 xs2
        ExtArray x1 == ExtArray x2 = x1 == x2
        ExtFunApp {n} x1 xs1 == ExtFunApp x2 xs2 = x1 == x2 && eqVect xs1 xs2
        FMul x1 y1 == FMul x2 y2 = x1 == x2 && y1 == y2
        FDiv x1 y1 == FDiv x2 y2 = x1 == x2 && y1 == y2
        FAdd x1 y1 == FAdd x2 y2 = x1 == x2 && y1 == y2
        FSub x1 y1 == FSub x2 y2 = x1 == x2 && y1 == y2
        Add x1 y1 == Add x2 y2 = x1 == x2 && y1 == y2
        Sub x1 y1 == Sub x2 y2 = x1 == x2 && y1 == y2
        Tuple {n} xs1 == Tuple xs2 = eqVect xs1 xs2
        Put x1 y1 z1 == Put x2 y2 z2 = x1 == x2 && y1 == y2 && z1 == z2
        IfFalse x1 e11 e12 == IfFalse x2 e21 e22 = x1 == x2 && e11 == e21 && e12 == e22
        IfEqi x1 y1 e11 e12 == IfEqi x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
        IfLEi x1 y1 e11 e12 == IfLEi x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
        IfEqf x1 y1 e11 e12 == IfEqf x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
        IfLEf x1 y1 e11 e12 == IfLEf x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
        (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) with (decEq x1 x2) | (assert_total decEq t1 t2)
                (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | Yes x1Eqx2 | Yes t1Eqt2 = e11 == e21 && (shift x1Eqx2 t1Eqt2 e12) == e22
                (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | No _ | _ = {-if x1 == x2 then warn "fuck! 1" False else-} False
                (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | _ | No _ = {-if t1 == t2 then warn "fuck! 2" False else-} False
        LetTmp x1 t1 e11 e12 == LetTmp x2 t2 e21 e22 = x1 == x2 && t1 == t2 && e11 == e21 && e12 == e22
        (==) (LetRec {arity'=arity'1} fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec {arity'=arity'2} fun2@(MkFunDef (f2, t2) args2 body2) e2) with (decEq f1 f2) | (assert_total decEq t1 t2) 
                (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 with (decEq arity'1 arity'2)
                    (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 | Yes arity'1eqarity'2 = fun1 == (rewrite arity'1eqarity'2 in fun2) && (shift f1Eqf2 t1Eqt2 e1) == e2
                    (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 | No _ = False
                (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | No _ | _  = {-if f1 == f2 then warn "fuck! 3" False else-} False
                (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | _ | No _  = {-if t1 == t2 then warn "fuck! 4" False else-} False
            
        (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) with (decEq k'1 k'2)
            (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 with (assert_total decEq xs1 (rewrite k'1Eqk'2 in xs2))
                (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 | Yes xs1Eqxs2 = y1 == y2 && assert_total (==) e1 (rewrite xs1Eqxs2 in e2)
                (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 | No _ = False
            (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | _ = False
        _ == _ = False

public export
(.newKey): (Info a) => KNormal a env -> a 
(.newKey) (U {key}) = key.new
(.newKey) (B _ {key}) = key.new
(.newKey) (I _{key}) = key.new
(.newKey) (Fl _ {key}) = key.new
(.newKey) (Var _ {key}) = key.new
(.newKey) (Get _ _ {key}) = key.new
(.newKey) (Neg _ {key}) = key.new
(.newKey) (FNeg _ {key}) = key.new
(.newKey) (App _ _ {key}) = key.new
(.newKey) (AppTmp _ _ {key}) = key.new
(.newKey) (ExtArray _ {key}) = key.new
(.newKey) (ExtFunApp _ _ {key}) = key.new
(.newKey) (FMul _ _ {key}) = key.new
(.newKey) (FDiv _ _ {key}) = key.new
(.newKey) (FAdd _ _ {key}) = key.new
(.newKey) (FSub _ _ {key}) = key.new
(.newKey) (Add _ _ {key}) = key.new
(.newKey) (Sub _ _ {key}) = key.new
(.newKey) (Tuple _ {key}) = key.new
(.newKey) (Put _ _ _ {key}) = key.new
(.newKey) (IfFalse _ _ _ {key}) = key.new
(.newKey) (IfEqi _ _ _ _ {key}) = key.new
(.newKey) (IfLEi _ _ _ _ {key}) = key.new
(.newKey) (IfEqf _ _ _ _ {key}) = key.new
(.newKey) (IfLEf _ _ _ _ {key}) = key.new
(.newKey) (Let _ _ _ _ {key}) = key.new
(.newKey) (LetTmp _ _ _ _ {key}) = key.new
(.newKey) (LetRec _ _ {key}) = key.new
(.newKey) (LetTuple _ _ _ {key}) = key.new


export
changeEnv: (env': Env) -> KNormal a env -> KNormal a env'
changeEnv env' (U {key}) = U {key}
changeEnv env' (B b {key}) = B b {key}
changeEnv env' (I i {key}) = I i {key}
changeEnv env' (Fl f {key}) = Fl f {key}
changeEnv env' (Var x {key}) = Var x {key}
changeEnv env' (Get x y {key}) = Get x y {key}
changeEnv env' (Neg x {key}) = Neg x {key}
changeEnv env' (FNeg x {key}) = FNeg x {key}
changeEnv env' (App x xs {key}) = App x xs {key}
changeEnv env' (AppTmp x xs {key}) = AppTmp x xs {key}
changeEnv env' (ExtArray x {key}) = ExtArray x {key}
changeEnv env' (ExtFunApp x xs {key}) = ExtFunApp x xs {key}
changeEnv env' (FMul x y {key}) = FMul x y {key}
changeEnv env' (FDiv x y {key}) = FDiv x y {key}
changeEnv env' (FAdd x y {key}) = FAdd x y {key}
changeEnv env' (FSub x y {key}) = FSub x y {key}
changeEnv env' (Add x y {key}) = Add x y {key}
changeEnv env' (Sub x y {key}) = Sub x y {key}
changeEnv env' (Tuple xs {key}) = Tuple xs {key}
changeEnv env' (Put x y z {key}) = Put x y z {key}
changeEnv env' (IfFalse x e1 e2 {key}) = IfFalse x (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (IfEqi x y e1 e2 {key}) = IfEqi x y (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (IfLEi x y e1 e2 {key}) = IfLEi x y (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (IfEqf x y e1 e2 {key}) = IfEqf x y (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (IfLEf x y e1 e2 {key}) = IfLEf x y (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (Let x t e1 e2 {key}) = Let x t (changeEnv env' e1) (changeEnv ((x, t)::env') e2) {key}
changeEnv env' (LetTmp x t e1 e2 {key}) = LetTmp x t (changeEnv env' e1) (changeEnv env' e2) {key}
changeEnv env' (LetRec (MkFunDef name args body) e2 {key}) = LetRec (MkFunDef name args (changeEnv (revAppend args (name::env')) body)) (changeEnv (name::env') e2) {key}
changeEnv env' (LetTuple xs y e {key}) = LetTuple xs y (changeEnv (revAppend xs env') e) {key}

total
fv: KNormal a env -> SortedSet Id
fv e = case e of
    U => SortedSet.empty 
    (B _) => SortedSet.empty
    (I _) => SortedSet.empty
    (Fl _) => SortedSet.empty 
    (ExtArray _) => SortedSet.empty
    (Neg x ) => singleton x
    (FNeg x) => singleton x
    (Var x) => singleton (MkId x)
    (Add x y) => SortedSet.fromList [x, y]
    (Sub x y) => SortedSet.fromList [x, y]
    (Get x y) => SortedSet.fromList [x, y]
    (FAdd x y) => SortedSet.fromList [x, y]
    (FSub x y) => SortedSet.fromList [x, y]
    (FMul x y) => SortedSet.fromList [x, y]
    (FDiv x y) => SortedSet.fromList [x, y]
    (Put x y z) => SortedSet.fromList [x, y, z]
    (IfFalse x e1 e2) => insert x (union (fv e1) (fv e2))
    (IfEqi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    (IfLEi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    (IfEqf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    (IfLEf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    (Let x t e1 e2) => union (fv e1) (delete (MkId x) (fv e2))
    (LetTmp x t e1 e2) => union (fv e1) (delete (MkId x) (fv e2))
    (LetRec (MkFunDef (f, _) args body) e2) => delete (MkId f) (union (fv e2) (difference (fv body) (fromList (toList ((MkId . fst) <$> args)))))
    (LetTuple xs y e') => insert y (difference (fv e') (fromList (toList ((MkId . fst) <$> xs))))
    (Tuple xs) => SortedSet.fromList (toList xs)
    (ExtFunApp _ xs) => SortedSet.fromList (toList xs)
    (App x xs) => SortedSet.fromList (MkId x :: (toList xs))
    (AppTmp x xs) => SortedSet.fromList (MkId x :: (toList xs))

wrap: String -> String 
wrap s = "[" ++ s ++ "]"

export
Interpolation (KNormal a env) where
    interpolate U = "()"
    interpolate (B b) = if b then "true" else "false"
    interpolate (I i) = show i
    interpolate (Fl f) = show f
    interpolate (Var x) = show x
    interpolate (Get x y) = "(\{x}.(\{y}))"
    interpolate (Neg x) = "(- \{x})"
    interpolate (FNeg x) = "(-. \{x})"
    interpolate (App x y) = showParens True "\{x} \{joinBy " " (toList (show <$> y))}"
    interpolate (AppTmp x y) = showParens True "\{x} \{joinBy " " (toList (show <$> y))}"
    interpolate (ExtArray x) = "(\{x} [@extarray])"
    interpolate (ExtFunApp x xs) = "((\{x} [@extfunc]) \{joinBy " " (toList (show <$> xs))})"
    interpolate (FMul x y) = "(\{x} *. \{y})"
    interpolate (FDiv x y) = "(\{x} /. \{y})"
    interpolate (FAdd x y) = "(\{x} +. \{y})"
    interpolate (FSub x y) = "(\{x} -. \{y})"
    interpolate (Add x y) = "(\{x} + \{y})"
    interpolate (Sub x y) = "(\{x} - \{y})"
    interpolate (Tuple xs) = showParens True "\{joinBy ", " (toList (map show xs))}"
    interpolate (Put x y z) = "(\{x}.(\{y}) <- \{z})"
    interpolate (IfFalse x e1 e2) = "(if (* IfFalse *) not \{x} then \{e1} else \{e2})"
    interpolate (IfEqi x y e1 e2) = "(if (* IfEqi *) \{x} = \{y} then \{e1} else \{e2})"
    interpolate (IfLEi x y e1 e2) = "(if (* IfLEi *) \{x} <= \{y} then \{e1} else \{e2})"
    interpolate (IfEqf x y e1 e2) = "(if (* IfEqf *) \{x} = \{y} then \{e1} else \{e2})"
    interpolate (IfLEf x y e1 e2) = "(if (* IfLEf *) \{x} <= \{y} then \{e1} else \{e2})"
    interpolate (Let x t e1 e2) = "(let \{x}: \{show t} = \{e1} in (* \{fvs} *)\n\{e2})"
    where 
        fvs: String
        fvs = let fv = show <$> SortedSet.toList (fv e2) in if [] == fv then "[]" else wrap (joinBy "; " fv)
    interpolate (LetTmp x t e1 e2) = "(let \{x}: \{show t} = \{e1} in (* \{fvs} *)\n\{e2})"
    where 
        fvs: String 
        fvs = let fv = show <$> SortedSet.toList (fv e2) in if [] == fv then "[]" else wrap (joinBy "; " fv)
    interpolate (LetRec (MkFunDef name args body) e2) = 
        let args = (show . fst) <$> args in "(let[@bodyfvs \{bodyfvs}] rec \{fst name} \{joinBy " " (toList args)} = \n\{body} in (* \{fvs} *) \n\{e2})"
        where 
            bodyfvs: String
            bodyfvs = let bodyfv = show <$> SortedSet.toList (difference (fv body) (fromList (toList ((MkId . fst) <$> args))))
                in if [] == bodyfv then "[]" else wrap (joinBy "; " bodyfv)
            fvs: String
            fvs = let fv = show <$> SortedSet.toList (fv e2) in if [] == fv then "[]" else wrap (joinBy "; " fv)
    interpolate (LetTuple xs y e') = "(let[@projections \{projections}] (\{joinBy ", " (toList (show <$> fst <$> xs))}) = \{y} in (* \{fvs} *)\n\{e'})"
    where
        projections: String
        projections = "[" ++ joinBy "; " ((\i => show "\{y}.\{show i}") <$> [0..pred (length xs)]) ++ "]"
        fvs: String
        fvs = let fv = show <$> SortedSet.toList (fv e')
            in if [] == fv then "[]" else wrap (joinBy "; " fv)

export 
Show (KNormal a env) where
    show e = interpolate e


gm: Type -> Type
gm = EitherT String (ReaderT (SortedMap NodeKeyType (List1 Ty)) (State Nat))

isLocal: {env: Env} -> (x: NonNullString) -> Bool 
isLocal x = case findIndex (\(x', _) => case x' of (VarName x' _) => x == x'; _ => False) env of Just _ => True; Nothing => False

mutual    
    total
    insert_let: (Info a) => {env: Env} -> (KNormal a env, Ty) -> 
    ((x: Id) -> {auto p: (IsKind x Temporary) `Either` (IsKind x Variable)} -> gm (KNormal a env, Ty)) -> gm (KNormal a env, Ty)
    insert_let (Var x, _) k = k (MkId x)
    insert_let (e, t) k = do
        let x = TmpName !get 
        modify (S)
        (e', t') <- k (MkId x)
        pure ((LetTmp {key=e.newKey} x t e e'), t')

    ||| transform to k-normal form
    g: (Info a) => {env: Env} -> Node a -> gm (KNormal a env, Ty)
    g (U {key}) = pure (U {key}, TyUnit)
    g (I {key} i) = pure (I {key} i, TyI32)
    g (B {key} b) = pure (B {key} b, TyBool)
    g (F {key} f) = pure (Fl {key} f, TyF32)
    g (Var {key} x) = do 
        case findIndex (\(x', _) => case x' of (VarName x' _) => x == x'; _ => False) env of
            Just idx => let (x, t) = index' env idx in pure (Var {key} x, t)
            Nothing => case lookup key.key !(lift ask) of
                Just (t@(TyFun _ _):::[]) => pure (Var {key} (ExtName x), t)
                Just (t@(TyArray _):::[]) => pure (ExtArray {key} x, t)
                Just (t:::[]) => throwError $ "external variable \{show x} must be a function or array, but got \{show t}"
                Just (t:::ts) => throwError $ "type of \{show x} is ambiguous: \{", " `joinBy` (show <$> forget (t:::ts))}"
                Nothing => throwError $ "variable \{show x} not found"
    g (Get {key} e1 e2) = do 
        (e1', t1) <- g e1
        case t1 of 
            TyArray t => insert_let (e1', t1) (\x => do 
                insert_let !(g e2) (\y => pure (Get {key} x y, t)))
            _ => throwError $ "g (Get {key} e1 e2): unreachable"
    g (Neg {key} e) = insert_let !(g e) (\x => pure (Neg {key} x, TyI32))
    g (FNeg {key} e) = insert_let !(g e) (\x => pure (FNeg {key} x, TyF32))
    g (App {key} e es) = case e of 
        Var (MkNonNullStr "Array.make") => impl e es (\t, _, xs => pure (ExtFunApp {key} create_array xs, t))
        Var (MkNonNullStr "Array.create") => impl e es (\t, _, xs => pure (ExtFunApp {key} create_array xs, t))
        _ => impl e es cont
    where 
        create_array: NonNullString 
        create_array = MkNonNullStr "create_array"
        lemma: (n: Nat) -> S n = n + 1
        lemma n = case plusSuccRightSucc n 0 of p => case plusZeroRightNeutral n of p' => replace {p=(\x => S x = n + 1)} p' p
        lemma': {len, m': Nat} -> (S n = S len + S m') -> S n = len + S (S m')
        lemma' p = case inj S p of p' => case plusSuccRightSucc len (S m') of p'' => rewrite p' in p''

        bind: {m, m', n: Nat} -> (p: S n = m + S m') -> 
        Vect m (Node a) -> Vect (S m') Id -> (Vect (S n) Id -> gm (KNormal a env, Ty)) -> gm (KNormal a env, Ty)
        bind p [] xs k = k (rewrite p in reverse xs)
        bind p (e::es) xs k = insert_let !(g e) (\x => bind (lemma' p) es (x::xs) k)

        impl: {n: Nat} -> Node a -> Vect (S n) (Node a) -> 
        (Ty -> (f: Id) -> {auto p: (IsKind f Temporary) `Either` (IsKind f Variable)} -> Vect (S n) Id -> gm (KNormal a env, Ty)) ->
        gm (KNormal a env, Ty)
        impl e es k = do
            v@(_, t) <- g e
            case t of
                TyFun _ t' => insert_let v (\f => insert_let !(g (head es)) (\x => bind (lemma n) (tail es) [x] (k t' f)))
                _ => throwError $ "g (App {key} e es): unreachable"
        
        cont: {n: Nat} -> Ty -> (f: Id) -> {auto p: (IsKind f Temporary) `Either` (IsKind f Variable)} -> Vect (S n) Id -> gm (KNormal a env, Ty)
        cont t f xs with (p)
            cont t (MkId f@(TmpName _)) xs | Left (IdIsKind (TmpName _)) = pure (AppTmp {key} f xs, t)
            cont t (MkId f@(VarName _ _)) xs | Right (IdIsKind (VarName _ _)) = pure (App {key} f xs, t)
            cont t (MkId (ExtName f)) xs | Right (IdIsKind (ExtName f)) = pure (ExtFunApp {key} f xs, t)
            cont t (MkId (RegName _)) xs | Left _ impossible
            cont t (MkId (RegName _)) xs | Right _ impossible
            cont t (MkId (MemName _ _)) xs | Left _ impossible
            cont t (MkId (MemName _ _)) xs | Right _ impossible

    g (FMul {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (FMul {key} x y, TyF32)))
    g (FDiv {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (FDiv {key} x y, TyF32)))
    g (FAdd {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (FAdd {key} x y, TyF32)))
    g (FSub {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (FSub {key} x y, TyF32)))
    g (Add {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (Add {key} x y, TyI32)))
    g (Sub {key} e1 e2) = insert_let !(g e1) (\x => insert_let !(g e2) (\y => pure (Sub {key} x y, TyI32)))
    g e@(Eq {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Neq {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Lt {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Le {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Gt {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Ge {key} _ _) = g (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g (Tuple {key} xs) = bind Refl [] [] xs
    where 
        lemma: {n, m, len: Nat} -> 2 + n = S m + len -> 2 + n = m + S len
        lemma p = case plusSuccRightSucc m len of p' => rewrite p in p'

        lemma': {n, len: Nat} -> {auto p: 2 + n = len} -> Vect len b -> Vect (2 + n) b
        lemma' xs = rewrite p in xs

        -- lemma''': {n, len: Nat} -> 2 + n = len -> Vect len Id -> Vect (2 + n) Id
        -- lemma''' p xs = rewrite p in xs
        bind: {n, m, len: Nat} -> (p: 2 + n = m + len) -> 
        Vect len Id -> Vect len Ty -> Vect m (Node a) -> gm (KNormal a env, Ty)
        bind {n, m=Z, len} p xs ts [] = pure (Tuple {key} (lemma' $ reverse xs), TyTuple (lemma' $ reverse ts))
        bind p xs ts (x::xs') = do
            v@(_, t) <- g x
            insert_let v (\x => bind (lemma p) (x::xs) (t::ts) xs')

    g (Put {key} e1 e2 e3) = 
        insert_let !(g e1) (\x => 
            insert_let !(g e2) (\y => 
                insert_let !(g e3) (\z => pure (Put {key} x y z, TyUnit))))
    g (If {key} (Eq e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyBool => pure (IfEqi {key} x y e3' e4', t)
                    TyI32 => pure (IfEqi {key} x y e3' e4', t)
                    TyF32 => pure (IfEqf {key} x y e3' e4', t)
                    _ => throwError "expected \{show e1} to be int, bool or float, but got \{show t1}"))
    g (If {key} (Neq e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyBool => pure (IfEqi {key} x y e4' e3', t)
                    TyI32 => pure (IfEqi {key} x y e4' e3', t)
                    TyF32 => pure (IfEqf {key} x y e4' e3', t)
                    _ => throwError "expected \{show e1} to be int, bool or float, but got \{show t1}"))
    g (If {key} (Le e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyI32 => pure (IfLEi {key} x y e3' e4', t)
                    TyF32 => pure (IfLEf {key} x y e3' e4', t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show t1}"))
    g (If {key} (Ge e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyI32 => pure (IfLEi {key} y x e3' e4', t)
                    TyF32 => pure (IfLEf {key} y x e3' e4', t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show t1}"))
    g (If {key} (Lt e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyI32 => pure (IfLEi {key} y x e4' e3', t)
                    TyF32 => pure (IfLEf {key} y x e4' e3', t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show t1}"))
    g (If {key} (Gt e1 e2) e3 e4) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            insert_let !(g e2) (\y => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case t1 of
                    TyI32 => pure (IfLEi {key} x y e4' e3', t)
                    TyF32 => pure (IfLEf {key} x y e4' e3', t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show t1}"))
    g e@(If {key} e1 e2 e3) = do
        v1@(_, t1) <- g e1
        insert_let v1 (\x => do
            (e2', t) <- g {env} e2
            (e3', _) <- g {env} e3
            case t1 of
                TyBool => pure (IfFalse {key} x e3' e2', t)
                _ => throwError "\{show @{a2} e1.getKey.span}\nexpected \{show e1} to be bool, but got \{show t1}")
    g (Semi {key} e1 e2) = do 
        (e1', t1) <- g e1
        (e2', t2) <- g {env} e2
        let name = TmpName !get
        modify (S)
        pure (LetTmp {key} name t1 e1' e2', t2)
    g (Let {key} x e1 e2) = do
        (e1', t1) <- g {env} e1
        let x = VarName x key.key
        (e2', t2) <- g {env=(x, t1)::env} e2
        pure (Let {key} x t1 e1' e2', t2)
    g (LetTuple {key} xs e1 e2) = do
        v1@(_, t1) <- g {env} e1
        case t1 of
            TyTuple {n} ts => (case exactLength (2 + n) xs of 
                Just xs =>
                    insert_let v1 (\y => do
                        let xs = (\x => VarName x key.key) <$> xs
                        let xts = zip xs ts
                        (e2', t2) <- g {env=revAppend xts env} e2
                        pure (LetTuple {key} xts y e2', t2))
                Nothing => throwError $ "different length of tuple: \{show t1} and \{show xs}")
            _ => throwError $ "expected \{show e1} to be tuple, but got \{show t1}"
    g (LetRec {key} (MkFunDef fkey name args body) e) = do
        case lookup fkey.key !(lift ask) of
            Just (tfun@(TyFun {n} targs tret):::[]) => case exactLength (1 + n) args of 
                Just args => do
                    let name = VarName name fkey.key
                    let args = (\x => VarName x key.key) <$> args
                    let args = zip args targs
                    (body', _) <- g {env=revAppend args ((name, tfun)::env)} body
                    let fdef = MkFunDef (name, tfun) args body'
                    (e', t) <- g {env=getName fdef :: env} e
                    pure (LetRec {key} fdef e', t)
                Nothing => throwError $ "different length of arguments: \{show tfun} and \{show args}"
            Just (t:::[]) => throwError $ "`\{name}` must be a function, but got type \{show t}"
            Just (t:::ts) => throwError $ "\{show @{a2} fkey.span}\nin letrec, type of `\{name}` is ambiguous: \{", " `joinBy` (show <$> forget (t:::ts))}"
            Nothing => throwError $ "function \{show name} not found"

export
f: (Info a) => SortedMap NodeKeyType (List1 Ty) -> Node a -> Either String (KNormal a [], Ty)
f nodesTy e = evalState Z (runReaderT nodesTy (runEitherT (g e)))