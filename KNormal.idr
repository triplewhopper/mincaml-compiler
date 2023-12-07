module KNormal

import Data.Vect
import Data.List
import Data.Vect.Quantifiers
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

In: (x: a) -> (t: b) -> (xs: List (a, b)) -> Type
In _ _ [] = Void
In x t ((x', t')::xys) = ((x, t) = (x', t')) `Either` (In x t xys)


public export 
revAppend: Vect n a -> List a -> List a 
revAppend [] ys = ys
revAppend (x::xs) ys = revAppend xs (x::ys)

public export
revAppendLemma: (xts: Vect n a) -> (ys: List a) -> length (revAppend xts ys) = length xts + length ys
revAppendLemma [] ys = Refl 
revAppendLemma (x::xs) ys = rewrite plusSuccRightSucc (length xs) (length ys) in revAppendLemma xs (x::ys)


public export 
data BiOp = ADD | SUB | MUL | DIV

mutual
    public export
    data KNormal: Type -> Type where
        U: {key: a} -> KNormal a
        B: {key: a} -> Bool -> KNormal a
        I: {key: a} -> Int -> KNormal a
        Fl: {key: a} -> Double -> KNormal a
        Var: {key: a} -> {-{env: Env} ->-} (x: IdName Variable) -> {t: Ty} -> {-{auto p: In (MkId x) t env} ->-} KNormal a
        Get: {key: a} -> {- {env: Env} -> -} (x: Id) -> (y: Id) -> {t: Ty} -> {-{auto p1: In x (TyArray t) env} -> {auto p2: In y TyI32 env} ->-} KNormal a
        Neg: {key: a} -> {- {env: Env} -> -} (x: Id) -> {t: Ty} -> {auto p: IsNumTy t} -> {-{auto p: In x TyI32 env} ->-} KNormal a
        -- FNeg: {key: a} -> {env: Env} -> (x: Id) -> {-{auto p: In x TyF32 env} ->-} KNormal a
        App: {key: a} -> {- {env: Env} -> -} (x: IdName Variable) -> {auto p: IsVarName x} -> {-{n: Nat} ->-} (arg: Id) -> {argty: Ty} -> {retty: Ty} -> {-{auto pArg: In arg argty env} -> {auto pFun: In x (TyFun argty retty) env} ->-} KNormal a
        AppTmp: {key: a} -> {- {env: Env} -> -} (x: IdName Temporary) -> {-{n: Nat} ->-} (arg: Id) -> {argty: Ty} -> {retty: Ty} {--> {auto pArgs: All (\(x, t) => In x t env) (zip args argty)} -> {auto pFun: In (MkId x) (TyFun argty retty) env}-} -> KNormal a
        -- AppTmp: {key: a} -> {env: Env} -> (x: IdName Temporary) -> {n: Nat} -> (args: Vect (1 + n) Id) -> {argty: Vect (1 + n) Ty} -> {retty: Ty} -> {auto pArgs: All (\(x, t) => In x t env) (zip args argty)} -> {auto pFun: In (MkId x) (TyFun argty retty) env} -> KNormal a
        ExtArray: {key: a} -> {- {env: Env} -> -} (x: NonNullString) -> {t: Ty} -> {t_: Ty} -> {auto p: t = (TyArray t_)} -> KNormal a
        ExtFunApp: {key: a} -> {- {env: Env} -> -} (x: NonNullString) {--> {n: Nat}-} -> (arg: Id) -> {argty: Ty} -> {retty: Ty} -> {-{funty: Ty} -> {auto pArg: In arg argty env} -> {auto pFun: funty = TyFun argty retty} ->-} KNormal a
        BinaryOp: {key: a} -> {- {env: Env} -> -} (op: BiOp) -> (x: Id) -> (y: Id) -> {t: Ty} -> {-{auto p1: In x t env} -> {auto p2: In y t env} ->-} {auto p3: IsNumTy t} -> KNormal a
        Tuple: {key: a} -> {- {env: Env} -> -} {n: Nat} -> (xs: Vect (2 + n) Id) -> {ts: Vect (2 + n) Ty} {--> {auto p: All (\(x, t) => In x t env) (zip xs ts)}-} -> KNormal a
        Put: {key: a} -> {- {env: Env} -> -} (x: Id) -> (y: Id) -> (z: Id) -> {tz: Ty} {--> {auto p1: In x (TyArray t) env} -> {auto p2: In y TyI32 env} -> {auto p3: In z t env} -}-> KNormal a
        IfFalse: {key: a} -> {- {env: Env} -> -} (x: Id) -> {- {auto pCond: In x TyBool env} ->-} KNormal a -> KNormal a -> KNormal a
        IfEq: {key: a} -> {- {env: Env} -> -} (x: Id) -> (y: Id) -> {t: Ty} -> {- {auto pCondx: In x t env} -> {auto pCondy: In y t env} ->-}  {auto isEq: IsEqTy t} -> KNormal a -> KNormal a -> KNormal a
        IfLE: {key: a} -> {- {env: Env} -> -} (x: Id) -> (y: Id) -> {t: Ty} -> {- {auto pCondx: In x t env} -> {auto pCondy: In y t env} ->-}  {auto isNum: IsNumTy t} -> KNormal a -> KNormal a -> KNormal a
        Let: {key: a} -> {- {env: Env} -> -} (x: IdName Variable) -> (t: Ty) -> (rhs: KNormal a) -> KNormal a {-((x, t)::env)-} -> KNormal a
        LetTmp: {key: a} -> (x: IdName Temporary) -> (t: Ty) -> KNormal a -> KNormal a -> KNormal a
        LetRec: {key: a} -> {- {env: Env} -> -} {arity': Nat} -> (f: KNormal.FunDef a {-env-} arity') -> KNormal a {-(cast (getName f) :: env)-}-> KNormal a
        LetTuple: {key: a} -> {- {env: Env} -> -} {k: Nat} -> (tup: Vect (2 + k) Binding) -> (y: Id) -> KNormal a {-(revAppend tup env)-}-> KNormal a

    public export
    record FunDef (a: Type) {-(env: Env)-} (arity': Nat) where
        constructor MkFunDef
        name : FunBinding arity'
        args : Vect (S arity') Binding   
        body : KNormal a {-(revAppend args (cast name::env))-}

    public export
    getName: KNormal.FunDef a {-env -} arity -> FunBinding arity
    getName (MkFunDef name _ _) = name


data InRange : Nat -> Nat -> Type where
    IsInRange : (x : Nat) -> (n <= x = True) -> (x <= m = True) -> InRange n m

-- shift: {x1, x2: IdName Variable} -> {t1, t2: Ty} -> 
-- (x1 = x2) -> (t1 = t2) -> KNormal a ((x1, t1)::env) -> KNormal a ((x2, t2)::env)
-- shift Refl Refl e = e

-- shiftWithArgs: {f1, f2: IdName Variable} -> {t1, t2: Ty} -> {args1, args2: Vect n Binding} ->
-- (f1 = f2) -> (t1 = t2) -> (args1 = args2) -> KNormal a (revAppend args1 ((f1, t1)::env)) -> KNormal a (revAppend args2 ((f2, t2)::env))
-- shiftWithArgs Refl Refl Refl e = e

eqVect: (Eq a) => {n, m: Nat} -> Vect n a -> Vect m a -> Bool 
eqVect xs ys with (decEq n m)
    eqVect xs ys | Yes nEqm = xs == (rewrite nEqm in ys)
    eqVect xs ys | No _ = False

-- mutual 
--     Eq (FunDef a env arity) where
--         MkFunDef name1 args1 body1 == MkFunDef (f2, t2) args2 body2 with (decEq f1 f2) | (assert_total decEq t1 t2)
--             MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 with (assert_total decEq args1 args2)
--                 MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 | Yes args1Eqargs2 = assert_total (==) (shiftWithArgs f1Eqf2 t1Eqt2 args1Eqargs2 body1) body2
--                 MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | Yes f1Eqf2 | Yes t1Eqt2 | No _ = {-if args1 == args2 then warn "fuck! 5" False else-} False
--             MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | No _ | _ = {-if f1 == f2 then warn "fuck! 6" False else-} False 
--             MkFunDef (f1, t1) args1 body1 == MkFunDef (f2, t2) args2 body2 | _ | No _ = {-if t1 == t2 then warn "fuck! 7" False else-} False 
--     export 
--     Eq (KNormal a) where 
--         U == U = True
--         B b1 == B b2 = b1 == b2
--         I i1 == I i2 = i1 == i2
--         Fl f1 == Fl f2 = f1 == f2
--         Var x1 == Var x2 = x1 == x2
--         Get x1 y1 == Get x2 y2 = x1 == x2 && y1 == y2
--         Neg x1 == Neg x2 = x1 == x2
--         FNeg x1 == FNeg x2 = x1 == x2
--         App x1 xs1 == App x2 xs2 = x1 == x2 && eqVect xs1 xs2
--         AppTmp x1 xs1 == AppTmp x2 xs2 = x1 == x2 && eqVect xs1 xs2
--         ExtArray x1 == ExtArray x2 = x1 == x2
--         ExtFunApp {n} x1 xs1 == ExtFunApp x2 xs2 = x1 == x2 && eqVect xs1 xs2
--         FMul x1 y1 == FMul x2 y2 = x1 == x2 && y1 == y2
--         FDiv x1 y1 == FDiv x2 y2 = x1 == x2 && y1 == y2
--         FAdd x1 y1 == FAdd x2 y2 = x1 == x2 && y1 == y2
--         FSub x1 y1 == FSub x2 y2 = x1 == x2 && y1 == y2
--         Add x1 y1 == Add x2 y2 = x1 == x2 && y1 == y2
--         Sub x1 y1 == Sub x2 y2 = x1 == x2 && y1 == y2
--         Tuple {n} xs1 == Tuple xs2 = eqVect xs1 xs2
--         Put x1 y1 z1 == Put x2 y2 z2 = x1 == x2 && y1 == y2 && z1 == z2
--         IfFalse x1 e11 e12 == IfFalse x2 e21 e22 = x1 == x2 && e11 == e21 && e12 == e22
--         IfEqi x1 y1 e11 e12 == IfEqi x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
--         IfLEi x1 y1 e11 e12 == IfLEi x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
--         IfEqf x1 y1 e11 e12 == IfEqf x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
--         IfLEf x1 y1 e11 e12 == IfLEf x2 y2 e21 e22 = x1 == x2 && y1 == y2 && e11 == e21 && e12 == e22
--         (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) with (decEq x1 x2) | (assert_total decEq t1 t2)
--                 (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | Yes x1Eqx2 | Yes t1Eqt2 = e11 == e21 && (shift x1Eqx2 t1Eqt2 e12) == e22
--                 (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | No _ | _ = {-if x1 == x2 then warn "fuck! 1" False else-} False
--                 (==) (Let x1 t1 e11 e12) (Let x2 t2 e21 e22) | _ | No _ = {-if t1 == t2 then warn "fuck! 2" False else-} False
--         LetTmp x1 t1 e11 e12 == LetTmp x2 t2 e21 e22 = x1 == x2 && t1 == t2 && e11 == e21 && e12 == e22
--         (==) (LetRec {arity'=arity'1} fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec {arity'=arity'2} fun2@(MkFunDef (f2, t2) args2 body2) e2) with (decEq f1 f2) | (assert_total decEq t1 t2) 
--                 (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 with (decEq arity'1 arity'2)
--                     (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 | Yes arity'1eqarity'2 = fun1 == (rewrite arity'1eqarity'2 in fun2) && (shift f1Eqf2 t1Eqt2 e1) == e2
--                     (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | Yes f1Eqf2 | Yes t1Eqt2 | No _ = False
--                 (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | No _ | _  = {-if f1 == f2 then warn "fuck! 3" False else-} False
--                 (==) (LetRec fun1@(MkFunDef (f1, t1) args1 body1) e1) (LetRec fun2@(MkFunDef (f2, t2) args2 body2) e2) | _ | No _  = {-if t1 == t2 then warn "fuck! 4" False else-} False
            
--         (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) with (decEq k'1 k'2)
--             (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 with (assert_total decEq xs1 (rewrite k'1Eqk'2 in xs2))
--                 (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 | Yes xs1Eqxs2 = y1 == y2 && assert_total (==) e1 (rewrite xs1Eqxs2 in e2)
--                 (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | Yes k'1Eqk'2 | No _ = False
--             (==) (LetTuple {k=k'1} xs1 y1 e1) (LetTuple {k=k'2} xs2 y2 e2) | _ = False
--         _ == _ = False

public export
(.newKey): (Info a) => KNormal a -> a 
(.newKey) (U {key}) = key.new
(.newKey) (B _ {key}) = key.new
(.newKey) (I _{key}) = key.new
(.newKey) (Fl _ {key}) = key.new
(.newKey) (Var _ {key}) = key.new
(.newKey) (Get _ _ {key}) = key.new
(.newKey) (Neg _ {key}) = key.new
-- (.newKey) (FNeg _ {key}) = key.new
(.newKey) (App _ _ {key}) = key.new
(.newKey) (AppTmp _ _ {key}) = key.new
(.newKey) (ExtArray _ {key}) = key.new
(.newKey) (ExtFunApp _ _ {key}) = key.new
(.newKey) (BinaryOp _ _ _ {key}) = key.new
-- (.newKey) (FMul _ _ {key}) = key.new
-- (.newKey) (FDiv _ _ {key}) = key.new
-- (.newKey) (FAdd _ _ {key}) = key.new
-- (.newKey) (FSub _ _ {key}) = key.new
-- (.newKey) (Add _ _ {key}) = key.new
-- (.newKey) (Sub _ _ {key}) = key.new
(.newKey) (Tuple _ {key}) = key.new
(.newKey) (Put _ _ _ {key}) = key.new
(.newKey) (IfFalse _ _ _ {key}) = key.new
(.newKey) (IfEq _ _ _ _ {key}) = key.new
(.newKey) (IfLE _ _ _ _ {key}) = key.new
-- (.newKey) (IfEqi _ _ _ _ {key}) = key.new
-- (.newKey) (IfLEi _ _ _ _ {key}) = key.new
-- (.newKey) (IfEqf _ _ _ _ {key}) = key.new
-- (.newKey) (IfLEf _ _ _ _ {key}) = key.new
(.newKey) (Let _ _ _ _ {key}) = key.new
(.newKey) (LetTmp _ _ _ _ {key}) = key.new
(.newKey) (LetRec _ _ {key}) = key.new
(.newKey) (LetTuple _ _ _ {key}) = key.new

total
fv: KNormal a -> SortedSet Id
fv U = SortedSet.empty 
fv (B _) = SortedSet.empty
fv (I _) = SortedSet.empty
fv (Fl _) = SortedSet.empty 
fv (ExtArray _) = SortedSet.empty
fv (Neg x) = singleton x
-- fv (FNeg x) = singleton x
fv (Var x) = singleton (MkId x)
fv (Get x y) = fromList [x, y]
fv (BinaryOp _ x y) = SortedSet.fromList [x, y]
    -- (Add x y) => SortedSet.fromList [x, y]
    -- (Sub x y) => SortedSet.fromList [x, y]
    -- (Get x y) => SortedSet.fromList [x, y]
    -- (FAdd x y) => SortedSet.fromList [x, y]
    -- (FSub x y) => SortedSet.fromList [x, y]
    -- (FMul x y) => SortedSet.fromList [x, y]
    -- (FDiv x y) => SortedSet.fromList [x, y]
fv (Put x y z) = SortedSet.fromList [x, y, z]
fv (IfFalse x e1 e2) = insert x (union (fv e1) (fv e2))
fv (IfEq x y e1 e2) = insert x (insert y (union (fv e1) (fv e2)))
fv (IfLE x y e1 e2) = insert x (insert y (union (fv e1) (fv e2)))
    -- (IfEqi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    -- (IfLEi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    -- (IfEqf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
    -- (IfLEf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
fv (Let x t e1 e2) = union (fv e1) (delete (MkId x) (fv e2))
fv (LetTmp x t e1 e2) = union (fv e1) (delete (MkId x) (fv e2))
fv (LetRec (MkFunDef (MkFunBinding f _ _) args body) e2) = delete (MkId f) (union (fv e2) (difference (fv body) (fromList (toList ((MkId . fst) <$> args)))))
fv (LetTuple xs y e') = insert y (difference (fv e') (fromList (toList ((MkId . fst) <$> xs))))
fv (Tuple xs) = SortedSet.fromList (toList xs)
fv (ExtFunApp _ x) = singleton x
fv (App x y) = fromList [MkId x, y]
fv (AppTmp x y) = fromList [MkId x, y]
    -- (AppTmp x xs) => SortedSet.fromList (MkId x :: (toList xs))

-- export
-- changeEnv: (env': Env) -> (kn: KNormal a) -> {auto p: All (toList (fv kn)) (\x => In x env')} -> KNormal a'
-- changeEnv env' (U {key}) = U {key}
-- changeEnv env' (B b {key}) = B b {key}
-- changeEnv env' (I i {key}) = I i {key}
-- changeEnv env' (Fl f {key}) = Fl f {key}
-- changeEnv env' (Var x {key}) = Var x {key}
-- changeEnv env' (Get x y {key}) = Get x y {key}
-- changeEnv env' (Neg x {key}) = Neg x {key}
-- changeEnv env' (FNeg x {key}) = FNeg x {key}
-- changeEnv env' (App x xs {key}) = App x xs {key}
-- changeEnv env' (AppTmp x xs {key}) = AppTmp x xs {key}
-- changeEnv env' (ExtArray x {key}) = ExtArray x {key}
-- changeEnv env' (ExtFunApp x xs {key}) = ExtFunApp x xs {key}
-- changeEnv env' (FMul x y {key}) = FMul x y {key}
-- changeEnv env' (FDiv x y {key}) = FDiv x y {key}
-- changeEnv env' (FAdd x y {key}) = FAdd x y {key}
-- changeEnv env' (FSub x y {key}) = FSub x y {key}
-- changeEnv env' (Add x y {key}) = Add x y {key}
-- changeEnv env' (Sub x y {key}) = Sub x y {key}
-- changeEnv env' (Tuple xs {key}) = Tuple xs {key}
-- changeEnv env' (Put x y z {key}) = Put x y z {key}
-- changeEnv env' (IfFalse x e1 e2 {key}) = IfFalse x (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (IfEqi x y e1 e2 {key}) = IfEqi x y (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (IfLEi x y e1 e2 {key}) = IfLEi x y (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (IfEqf x y e1 e2 {key}) = IfEqf x y (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (IfLEf x y e1 e2 {key}) = IfLEf x y (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (Let x t e1 e2 {key}) = Let x t (changeEnv env' e1) (changeEnv ((x, t)::env') e2) {key}
-- changeEnv env' (LetTmp x t e1 e2 {key}) = LetTmp x t (changeEnv env' e1) (changeEnv env' e2) {key}
-- changeEnv env' (LetRec (MkFunDef name args body) e2 {key}) = LetRec (MkFunDef name args (changeEnv (revAppend args (cast name::env')) body)) (changeEnv (cast name::env') e2) {key}
-- changeEnv env' (LetTuple xs y e {key}) = LetTuple xs y (changeEnv (revAppend xs env') e) {key}


wrap: String -> String 
wrap s = "[" ++ s ++ "]"

export
Interpolation (KNormal a) where
    interpolate U = "()"
    interpolate (B b) = if b then "true" else "false"
    interpolate (I i) = show i
    interpolate (Fl f) = show f
    interpolate (Var x) = show x
    interpolate (Get x y) = "(\{x}.(\{y}))"
    interpolate (Neg x) = "(- \{x})"
    -- interpolate (FNeg x) = "(-. \{x})"
    -- interpolate (App x y) = showParens True "\{x} \{joinBy " " (toList (show <$> y))}"
    interpolate (App x y) = "(\{x} \{y})"
    interpolate (AppTmp x y) = "(\{x} \{y})"
    -- interpolate (AppTmp x y) = showParens True "\{x} \{joinBy " " (toList (show <$> y))}"
    interpolate (ExtArray x) = "(\{x} [@extarray])"
    -- interpolate (ExtFunApp x xs) = "((\{x} [@extfunc]) \{joinBy " " (toList (show <$> xs))})"
    interpolate (ExtFunApp x y) = "((\{x} [@extfunc]) \{y})"
    interpolate (BinaryOp MUL x y {t=TyF32}) = "(\{x} *. \{y})"
    interpolate (BinaryOp DIV x y {t=TyF32}) = "(\{x} /. \{y})"
    interpolate (BinaryOp ADD x y {t=TyF32}) = "(\{x} +. \{y})"
    interpolate (BinaryOp SUB x y {t=TyF32}) = "(\{x} -. \{y})"
    interpolate (BinaryOp ADD x y {t=TyI32}) = "(\{x} + \{y})"
    interpolate (BinaryOp SUB x y {t=TyI32}) = "(\{x} - \{y})"
    interpolate (BinaryOp MUL x y {t=TyI32}) = "(\{x} * \{y})"
    interpolate (BinaryOp DIV x y {t=TyI32}) = "(\{x} / \{y})"
    interpolate (Tuple xs) = showParens True "\{joinBy ", " (toList (map show xs))}"
    interpolate (Put x y z) = "(\{x}.(\{y}) <- \{z})"
    interpolate (IfFalse x e1 e2) = "(if (* IfFalse *) not \{x} then \{e1} else \{e2})"
    interpolate (IfEq x y e1 e2 {t}) = "(if (* IfEq \{show t} *) \{x} = \{y} then \{e1} else \{e2})"
    interpolate (IfLE x y e1 e2 {t}) = "(if (* IfLE \{show t} *) \{x} <= \{y} then \{e1} else \{e2})"
    interpolate (Let x t e1 e2) = "(let \{x}: \{show t} = \{e1} in (* \{fvs} *)\n\{e2})"
    where 
        fvs: String
        fvs = let fv = show <$> SortedSet.toList (fv e2) in if [] == fv then "[]" else wrap (joinBy "; " fv)
    interpolate (LetTmp x t e1 e2) = "(let \{x}: \{show t} = \{e1} in (* \{fvs} *)\n\{e2})"
    where 
        fvs: String 
        fvs = let fv = show <$> SortedSet.toList (fv e2) in if [] == fv then "[]" else wrap (joinBy "; " fv)
    interpolate (LetRec (MkFunDef fn args body) e2) = 
        let args = (show . fst) <$> args in "(let[@bodyfvs \{bodyfvs}] rec \{fn.name} \{joinBy " " (toList args)} = \n\{body} in (* \{fvs} *) \n\{e2})"
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
Show (KNormal a) where
    show e = interpolate e


gm: Type -> Type
gm = EitherT String (ReaderT (SortedMap NodeKeyType (List1 Ty)) (State Nat))

isLocal: {env: Env} -> (x: NonNullString) -> Maybe (DPair (IdName Variable, Ty) (\(x, t) => In x t env))
isLocal {env=[]} x = Nothing
isLocal {env=(x', t)::xs} x with ((x', t)) proof prf
    isLocal {env=(x', t)::xs} x | ((VarName s _), _) with (decEq x s)
        isLocal {env=(x', t)::xs} x | ((VarName s _), t) | Yes xEqs = Just ((x', t) ** Left prf)
        isLocal {env=(x', t)::xs} x | ((VarName _ _), t) | No _ = case isLocal {env=xs} x of 
            Just ((x'', t'') ** p) => Just ((x'', t'') ** Right p)
            Nothing => Nothing
    isLocal {env=(x', t)::xs} x | (_, _) = case isLocal {env=xs} x of 
        Just ((x'', t'') ** p) => Just ((x'', t'') ** Right p)
        Nothing => Nothing

mutual    
    total
    insert_let: (Info a) => {-{env: Env} ->-} (KNormal a, Ty) -> 
    ({-{env: Env} ->-} (x: Id) -> (t: Ty) {--> In x t env-} -> gm (KNormal a, Ty)) -> gm (KNormal a, Ty)
    insert_let (Var x {t}, _) k = k (MkId x) t
    insert_let (e, t) k = do
        let x = TmpName !get 
        modify (S)
        (e', t') <- k (MkId x) t
        pure ((LetTmp {key=e.newKey} x t e e'), t')

    ||| transform to k-normal form
    g: (Info a) => {env: Env} -> Node a -> gm (KNormal a, Ty)
    g (U {key}) = pure (U {key}, TyUnit)
    g (I i {key}) = pure (I i {key}, TyI32)
    g (B b {key}) = pure (B b {key}, TyBool)
    g (F f {key}) = pure (Fl f {key}, TyF32)
    g (Var x {key}) = do 
        case isLocal x {env} of
            Just ((x, t) ** p) => pure (Var x {key, t}, t)
            Nothing => case lookup key.key !(lift ask) of
                Just (t@(TyFun _ _):::[]) => pure (Var {key, t} (ExtName x), t)
                Just (t@(TyArray _):::[]) => pure (ExtArray {key, t} x, t)
                Just (t:::[]) => throwError $ "external variable \{show x} must be a function or array, but got \{show t}"
                Just (t:::ts) => throwError $ "type of \{show x} is ambiguous: \{", " `joinBy` (show <$> forget (t:::ts))}"
                Nothing => throwError $ "variable \{show x} not found"
    g (Get e1 e2 {key}) = do  
        insert_let !(g e1 {env}) (\x, tx => do 
            case tx of 
                TyArray t => insert_let !(g e2 {env}) (\y, _ => pure (Get x y {key, t}, t))
                _ => throwError $ "g (Get {key} e1 e2): unreachable")
    -- where
    --     cont1: (Info a) => {env: Env} -> (x: Id) -> (t: Ty) -> In x t env-> gm (KNormal a, Ty)
    --     cont1 {env} x t px with (t)
    --         cont1 {env} x t px | TyArray t' = insert_let !(g e2 {env}) cont2 where
    --             cont2: (Info a) => (y: Id) -> (t: Ty) -> In y t env-> gm (KNormal a, Ty)
    --             cont2 y TyI32 py = pure (Get {key} x y {env} {t=t'} {p1=px} {p2=py}, t')
    --             cont2 y t py = throwError $ "g (Get {key} e1 e2): unreachable"
    --         cont1 {env} x t px | _ = throwError $ "g (Get {key} e1 e2): unreachable"
    g (Neg e {key}) = insert_let !(g e {env}) (\x, t => case t of 
        TyI32 => pure (Neg x {key, t=TyI32}, TyI32)
        TyF32 => pure (Neg x {key, t=TyF32}, TyF32)
        _ => throwError $ "g (Neg {key} e): unreachable")
    g (FNeg e {key}) = insert_let !(g e {env}) (\x, _ => pure (Neg x {key, t=TyF32}, TyF32))
    g (App e es {key}) = case e of 
        Var {key=key'} (MkNonNullStr "Array.make") => impl (Var {key=key'} create_array) es cont
        Var {key=key'} (MkNonNullStr "Array.create") => impl (Var {key=key'} create_array) es cont
        _ => impl e es cont
    where 
        create_array: NonNullString 
        create_array = MkNonNullStr "create_array"
        lemma: (n: Nat) -> S n = n + 1
        lemma n = case plusSuccRightSucc n 0 of p => case plusZeroRightNeutral n of p' => replace {p=(\x => S x = n + 1)} p' p
        lemma': {len, m': Nat} -> (S n = S len + S m') -> S n = len + S (S m')
        lemma' p = case inj S p of p' => case plusSuccRightSucc len (S m') of p'' => rewrite p' in p''

        bind: {m, m', n: Nat} -> 
        (p: S n = m + S m') -> Vect m (Node a) -> Vect (S m') Id -> Vect (S m') Ty -> (Vect (S n) Id -> Vect (S n) Ty -> gm (KNormal a, Ty)) -> gm (KNormal a, Ty)
        bind p [] xs ts k = k (rewrite p in reverse xs) (rewrite p in reverse ts)
        bind p (e::es) xs ts k = insert_let !(g e {env}) (\x, t => bind (lemma' p) es (x::xs) (t::ts) k)

        impl: {n: Nat} -> Node a -> Vect (S n) (Node a) -> 
        (Ty -> (f: Id) -> Vect (S n) Id -> Vect (S n) Ty -> gm (KNormal a, Ty)) ->
        gm (KNormal a, Ty)
        impl e es k = do
            v@(_, t) <- g e {env}
            case t of
                TyFun _ t' => insert_let v (\f,_ => insert_let !(g (head es) {env}) (\x, tx => bind (lemma n) (tail es) [x] [tx] (k t' f)))
                _ => throwError $ "g (App {key} e es): unreachable"
        
        cont: {n: Nat} -> Ty -> (f: Id) -> Vect (S n) Id -> Vect (S n) Ty -> gm (KNormal a, Ty)
        cont retty (MkId f@(TmpName _)) [x] [argty] = pure (AppTmp {key} f x {argty, retty}, retty)
        cont retty (MkId f@(VarName _ _)) [x] [argty]= pure (App {key} f x {argty, retty}, retty)
        cont retty (MkId (ExtName f)) [x] [argty] = pure (ExtFunApp {key} f x {argty, retty}, retty)
        cont retty (MkId f@(TmpName _)) xs@(_::_::_) ts@(_::_::_) = do 
            let arg = TmpName !get
            let argty = TyTuple ts
            modify S
            pure (LetTmp {key=key.new} arg argty (Tuple {key=key.new, ts} xs) (AppTmp {key} f (MkId arg) {argty, retty}), retty)
        cont retty (MkId f@(VarName _ _)) xs@(_::_::_) ts@(_::_::_) = do 
            let arg = TmpName !get
            let argty = TyTuple ts
            modify S
            pure (LetTmp {key=key.new} arg argty (Tuple {key=key.new, ts} xs) (App {key} f (MkId arg) {argty, retty}), retty)
        cont retty (MkId (ExtName f)) xs@(_::_::_) ts@(_::_::_) = do 
            let arg = TmpName !get
            let argty = TyTuple ts
            modify S
            pure (LetTmp {key=key.new} arg argty (Tuple {key=key.new, ts} xs) (ExtFunApp {key} f (MkId arg) {argty, retty}), retty)

    g (FMul {key} e1 e2) = insert_let !(g e1 {env}) (\x, _ => insert_let !(g e2 {env}) (\y, _ => pure (BinaryOp MUL x y {key, t=TyF32}, TyF32)))
    g (FDiv {key} e1 e2) = insert_let !(g e1 {env}) (\x, _ => insert_let !(g e2 {env}) (\y, _ => pure (BinaryOp DIV x y {key, t=TyF32}, TyF32)))
    g (FAdd {key} e1 e2) = insert_let !(g e1 {env}) (\x, _ => insert_let !(g e2 {env}) (\y, _ => pure (BinaryOp ADD x y {key, t=TyF32}, TyF32)))
    g (FSub {key} e1 e2) = insert_let !(g e1 {env}) (\x, _ => insert_let !(g e2 {env}) (\y, _ => pure (BinaryOp SUB x y {key, t=TyF32}, TyF32)))
    g (Add {key} e1 e2) = insert_let !(g e1 {env}) (\x, tx => 
        insert_let !(g e2 {env}) (\y, ty => 
            case (tx, ty) of 
                (TyI32, TyI32) => pure (BinaryOp ADD x y {key, t=TyI32}, TyI32)
                (TyF32, TyF32) => pure (BinaryOp ADD x y {key, t=TyF32}, TyF32)
                _ => throwError $ "expected \{show e1} and \{show e2} to be int or float, but got \{show tx} and \{show ty}"))
    g (Sub {key} e1 e2) = insert_let !(g e1 {env}) (\x, tx => 
        insert_let !(g e2 {env}) (\y, ty => 
            case (tx, ty) of 
                (TyI32, TyI32) => pure (BinaryOp SUB x y {key, t=TyI32}, TyI32)
                (TyF32, TyF32) => pure (BinaryOp SUB x y {key, t=TyF32}, TyF32)
                _ => throwError $ "expected \{show e1} and \{show e2} to be int or float, but got \{show tx} and \{show ty}"))
    g e@(Eq {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Neq {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Lt {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Le {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Gt {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g e@(Ge {key} _ _) = g {env} (If {key} e (B {key=key.new} True) (B {key=key.new} False))
    g (Tuple {key} xs) = bind Refl [] [] xs
    where 
        lemma: {n, m, len: Nat} -> 2 + n = S m + len -> 2 + n = m + S len
        lemma p = case plusSuccRightSucc m len of p' => rewrite p in p'

        lemma': {n, len: Nat} -> {auto p: 2 + n = len} -> Vect len b -> Vect (2 + n) b
        lemma' xs = rewrite p in xs

        -- lemma''': {n, len: Nat} -> 2 + n = len -> Vect len Id -> Vect (2 + n) Id
        -- lemma''' p xs = rewrite p in xs
        bind: {n, m, len: Nat} -> 
        (p: 2 + n = m + len) -> Vect len Id -> Vect len Ty -> Vect m (Node a) -> gm (KNormal a, Ty)
        bind {n, m=Z, len} p xs ts [] = let ts = lemma' (reverse ts) in pure (Tuple {key, ts} (lemma' $ reverse xs), TyTuple ts)
        bind p xs ts (x::xs') = insert_let !(g x {env}) (\x, t => bind (lemma p) (x::xs) (t::ts) xs')

    g (Put {key} e1 e2 e3) = 
        insert_let !(g e1 {env}) (\x, _ => 
            insert_let !(g e2 {env}) (\y, _ => 
                insert_let !(g e3 {env}) (\z, tz => pure (Put {key} x y z {tz}, TyUnit))))
    g (If {key} (Eq e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _ => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyBool => pure (IfEq {key} x y e3' e4' {t=tx}, t)
                    TyI32 => pure (IfEq {key} x y e3' e4' {t=tx}, t)
                    TyF32 => pure (IfEq {key} x y e3' e4' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int, bool or float, but got \{show tx}"))
    g (If {key} (Neq e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _ => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyBool => pure (IfEq {key} x y e4' e3' {t=tx}, t)
                    TyI32 => pure (IfEq {key} x y e4' e3' {t=tx}, t)
                    TyF32 => pure (IfEq {key} x y e4' e3' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int, bool or float, but got \{show tx}"))
    g (If {key} (Le e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _ => do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyI32 => pure (IfLE {key} x y e3' e4' {t=tx}, t)
                    TyF32 => pure (IfLE {key} x y e3' e4' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show tx}"))
    g (If {key} (Ge e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _=> do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyI32 => pure (IfLE {key} y x e3' e4' {t=tx}, t)
                    TyF32 => pure (IfLE {key} y x e3' e4' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show tx}"))
    g (If {key} (Lt e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _=> do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyI32 => pure (IfLE {key} y x e4' e3' {t=tx}, t)
                    TyF32 => pure (IfLE {key} y x e4' e3' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show tx}"))
    g (If {key} (Gt e1 e2) e3 e4) = do
        insert_let !(g e1 {env}) (\x, tx => do
            insert_let !(g e2 {env}) (\y, _=> do
                (e3', t) <- g {env} e3
                (e4', _) <- g {env} e4
                case tx of
                    TyI32 => pure (IfLE {key} x y e4' e3' {t=tx}, t)
                    TyF32 => pure (IfLE {key} x y e4' e3' {t=tx}, t)
                    _ => throwError "expected \{show e1} to be int or float, but got \{show tx}"))
    g e@(If {key} e1 e2 e3) = do
        insert_let !(g e1 {env}) (\x, t1 => do
            (e2', t) <- g {env} e2
            (e3', _) <- g {env} e3
            case t1 of
                TyBool => pure (IfFalse {key} x e3' e2', t)
                _ => throwError "\{show @{a2} e1.getKey.span}\nexpected \{show e1} to be bool, but got \{show t1}")
    g (Semi {key} e1 e2) = do 
        (e1', t1) <- g e1 {env}
        (e2', t2) <- g e2 {env}
        let name = TmpName !get
        modify (S)
        pure (LetTmp {key} name t1 e1' e2', t2)
    g (Let {key} x e1 e2) = do
        (e1', t1) <- g {env} e1
        let x = VarName x key.key
        (e2', t2) <- g {env=(x, t1)::env} e2
        pure (Let {key} x t1 e1' e2', t2)
    g (LetTuple {key} xs e1 e2) = do
        insert_let !(g e1 {env}) (\y, t1 => case t1 of
            TyTuple {n} ts => (case exactLength (2 + n) xs of 
                Just xs => do
                    let xs = (\x => VarName x key.key) <$> xs
                    let xts = zip xs ts
                    (e2', t2) <- g {env=revAppend xts env} e2
                    pure (LetTuple {key} xts y e2', t2)
                Nothing => throwError $ "different length of tuple: \{show t1} and \{show xs}")
            _ => throwError $ "expected \{show e1} to be tuple, but got \{show t1}")
    g (LetRec {key} (MkFunDef fkey name args body) e) = do
        case lookup fkey.key !(lift ask) of
            Just (tfun@(TyFun _ _):::[]) => do 
                (n ** (targs, tret)) <- case unpack (length args) tfun of
                    Just x => pure x
                    Nothing => throwError $ "g (LetRec {key} (MkFunDef fkey name args body) e): unreachable"
                case exactLength (1 + n) args of 
                    Just args => do
                        let name = VarName name fkey.key
                        let args = (\x => VarName x key.key) <$> args
                        let args = zip args targs
                        let fnbd = MkFunBinding name targs tret
                        (body', _) <- g {env=revAppend args (cast fnbd ::env)} body
                        let fdef = MkFunDef fnbd args body'
                        (e', t) <- g {env=cast (getName fdef) :: env} e
                        pure (LetRec {key} fdef e', t)
                    Nothing => throwError $ "different length of arguments: \{show tfun} and \{show args}"
            Just (t:::[]) => throwError $ "`\{name}` must be a function, but got type \{show t}"
            Just (t:::ts) => throwError $ "\{show @{a2} fkey.span}\nin letrec, type of `\{name}` is ambiguous: \{", " `joinBy` (show <$> forget (t:::ts))}"
            Nothing => throwError $ "function \{show name} not found"
        where
            ||| unpack function type
            ||| e.g. 
            ||| unpack 3 (a -> b -> c -> d) = Just (2 ** ([a, b, c], d))
            ||| unpack 2 (a -> b -> c -> d) = Just (1 ** ([a, b], c -> d))
            ||| unpack 1 (a -> b -> c -> d) = Just (0 ** ([a], b -> c -> d))
            unpack: Nat -> Ty -> Maybe (n: Nat ** (Vect (S n) Ty, Ty))
            unpack Z (TyFun a b) = Just (Z ** ([a], b))
            unpack (S k) (TyFun a b) = case unpack k b of
                Just (n ** (ts, ret)) => Just (S n ** (a::ts, ret))
                Nothing => Just (Z ** ([a], b))
            unpack _ _ = Nothing

export
f: (Info a) => SortedMap NodeKeyType (List1 Ty) -> Node a -> Either String (KNormal a, Ty)
f nodesTy e = evalState Z (runReaderT nodesTy (runEitherT (g e {env=[]})))