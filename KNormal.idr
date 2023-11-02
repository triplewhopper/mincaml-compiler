module KNormal

import Data.Vect
import Data.List
import Data.List.Elem
import Data.List.HasLength
import Data.Fun
import Data.String
import Data.Nat.Order
import Data.SortedSet as SortedSet
import Decidable.Equality
import Data.HVect
import Ty
import Id
import Cyntax as Syntax


%default total

-- mutual
--     DecEq (t: Type ** Ty t) where
--         decEq (_ ** TyI32) (_ ** TyI32) = Yes Refl
--         decEq (_ ** TyF32) (_ ** TyF32) = Yes Refl
--         decEq (_ ** TyUnit) (_ ** TyUnit) = Yes Refl
--         decEq (_ ** TyBool) (_ ** TyBool) = Yes Refl
--         decEq (_ ** TyTuple {n=n1} xs) (_ ** TyTuple {n=n2} ys) with (decEq n1 n2)
--             decEq (_ ** TyTuple {n=n1} xs) (_ **  TyTuple {n=n2} ys) | Yes h = let h': Dec (xs = ys) = Lemma4 xs ys h in ?jjj
--             decEq (_ ** TyTuple xs) (_ ** TyTuple ys) | No _ = No ?wtf2
--         -- decEq (_ ** TyTuple {n=n1} xs) (_ ** TyTuple {n=n2} ys) with (decEq (length xs) (length ys))
--         --     decEq (_ ** TyTuple {n=n1} xs) (_ ** TyTuple {n=n2} ys) | Yes h = 
--         --         case lengthCorrect xs of 
--         --             h0 => case lengthCorrect ys of 
--         --                 h1 => case Lemma1 xs ys (sym h0) (sym h1) h of 
--         --                     h2 => let ys' = rewrite h2 in ys in case decEq xs ys' of 
--         --                         Yes h3 => decEqCong2 ?jj ?ll
--         --                         No fuck => No ?wtf
--             -- decEq (_ ** TyTuple xs) (_ ** TyTuple ys) | No fuck = ?wtf
--         decEq (_ ** TyArray a) (_ ** TyArray b) = ?wtff
--         -- decEq (_ ** TyFun {n=n1} xs x) (_ ** TyFun (n2 ** ys) y) =  exactLength n2 xs == Just ys && x == y
--         --  with (decEq n1 n2)
--         --     decEq (_ ** TyFun {n=n1} xs x) (_ ** TyFun (n1 ** ys) y) | Yes Refl = x == y && xs == ys
--         --     _ | No _ = False
--         decEq x y = ?dontknow

--     Lemma4: (xs: Vect (S (S n1)) (t: Type ** Ty t)) -> (ys: Vect (S (S n2)) (t: Type ** Ty t)) -> (h: n1 = n2) -> Dec (xs = ys)
--     Lemma4 xs ys h with (h)
--         Lemma4 xs ys _ | Refl = decEq xs ys

--     Lemma5: (x1: (t: Type ** Ty t)) -> (x2: (t: Type ** Ty t)) -> Dec ((fst x1) = (fst x2)) -> Dec(x1 = x2)
--     Lemma5 (t1 ** ty1) (t2 ** ty2) h with (h)
--         Lemma5 (t1 ** ty1) (t2 ** ty2) _ | Yes h' = Yes Refl
--         Lemma5 (t1 ** ty1) (t2 ** ty2) _ | No contra = No (\con => ?hjk)

--     -- Lemma6: {t1: Type} -> {t2: Type} -> (ty1: Ty t1) -> (ty2: Ty t2) -> (t1 = t2) -> (ty1 = ty2)
--     -- Lemma6 ty1 ty2 h with (h)
--     --     Lemma6 ty1 ty2 _ | ?h77 = ?hjkl

-- ConCatNullRightNeutral: (s: String) -> ((s ++ "") = s)
-- ConCatNullRightNeutral s = believe_me Refl
-- ConCatNullLeftNeutral: (s: String) -> (("" ++ s) = s)
-- ConCatNullLeftNeutral s = believe_me Refl

-- ConsConcatCommutative: (x: Char) -> (xs: String) -> (ys: String) -> ((strCons x xs) ++ ys = (strCons x (xs ++ ys)))
-- ConsConcatCommutative x xs ys = believe_me Refl

-- ConCatNotEmpty: (s1: String) -> (s2: String) -> ((not (null s1) = True) `Either` (not (null s2) = True)) -> (not (s1 ++ s2 == "") =True)
-- ConCatNotEmpty s1 s2 p = believe_me Refl



-- DecEq (name = "" -> Void) where
--     decEq p1 p2 = believe_me Refl

-- DecEq (IdName Variable) where 
--     decEq (VarName {p=p1} n1) (VarName {p=p2} n2) with (decEq n1 n2)
--         decEq (VarName {p=p1} n1) (VarName {p=p2} n1) | Yes Refl with (decEq p1 p2)
--             decEq (VarName {p=p1} n1) (VarName {p=p1} n1) | Yes Refl | Yes Refl = Yes Refl
--             decEq (VarName {p=p1} n1) (VarName {p=p2} n2) | Yes Refl | No contra = No (\con => ?wtf)
--         decEq (VarName n1) (VarName n2) | No contra = No (\con => ?wtf2)

-- DecEq Id where
--     decEq (MkId (k1 ** n1)) (MkId (k2 ** n2)) with (decEq k1 k2)
--         decEq (MkId (k1 ** n1)) (MkId (k1 ** n2)) | Yes Refl with (decEq n1 n2)
--             decEq (MkId (k1 ** n1)) (MkId (k1 ** n1)) | Yes Refl | Yes Refl = Yes Refl
--             decEq (MkId (k1 ** n1)) (MkId (k2 ** n2)) | Yes Refl | No contra = No (\con => ?wtf)
--         decEq (MkId (k1 ** n1)) (MkId (k2 ** n2)) | No contra = No (\con => ?wtf2)


-- II: (t: Type ** Ty t)
-- II = (Int ** TyI32)
-- F: (t: Type ** Ty t)
-- F = (Double ** TyF32)
-- B: (t: Type ** Ty t)
-- B = (Bool ** TyBool)
-- UU: (t: Type ** Ty t)
-- UU = (() ** TyUnit)

EnvEntry: Type
EnvEntry = ((x: Id ** IsKind x Variable), Ty)

Env: Type
Env = List EnvEntry

In: (x: a) -> (xs: List a) -> Type
In x [] = Void
In x (y::ys) = (x = y) `Either` (In x ys)


InKey: (x: Id) -> (xs: List (Id, _)) -> Type
InKey x [] = Void
InKey x ((y, _)::ys) = (x = y) `Either` (InKey x ys)

-- In_example_2: InKey n [("22", 2), ("44", 5)] -> (n': String ** n = n' ++ n')
-- In_example_2 (Left Refl) = ("2" ** Refl)
-- In_example_2 (Right $ Left Refl) = ("4" ** Refl)
-- In_example_2 (Right $ Right prf) = absurd prf

-- EnvElem: Id -> (t: Type ** Ty t) -> Env -> Type
-- EnvElem x t [] = Void
-- EnvElem x t ((y, u)::ys) = (x = y) `Either` ((t = u, EnvElem x t ys) `Either` Void)

-- In_map: (f: a -> b) -> (l: List a) -> (x: a ** Elem x l) -> Elem (f x) (map f l)
-- In_map _ [] (_ ** ixl) = absurd ixl
-- In_map f (x::xs) (x ** prf) = rewrite (f x) in Here

-- EnvTupleElem: Id -> Nat -> Env -> Type
-- EnvTupleElem x n [] = Void
-- EnvTupleElem x n ((y, u)::ys) = if x == y then case u of
--     (_ ** TyTuple ts) => (if n == length ts then True = True else Void)
--     _ => Void
--     else EnvTupleElem x n ys


mutual
    data KNormal: (env: Env) -> Type where
        U: KNormal env
        I: Int -> KNormal env
        Fl: Double -> KNormal env
        Neg: {env: Env} -> (x: Id) -> KNormal env
        Add: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        Sub: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        FNeg: {env: Env} -> (x: Id) -> KNormal env
        FAdd: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        FSub: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        FMul: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        FDiv: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        IfEqi: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env -> KNormal env -> KNormal env
        IfLEi: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env -> KNormal env -> KNormal env
        IfEqf: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env -> KNormal env -> KNormal env
        IfLEf: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env -> KNormal env -> KNormal env
        Let: {env: Env} -> (x: Id) -> {auto p: IsKind x Variable} -> (t: Ty) -> KNormal env -> KNormal (((x ** p), t)::env) -> KNormal env
        LetTmp: {env: Env} -> (x: Id) -> {auto p: IsKind x Temporary} -> (t: Ty) -> KNormal env -> KNormal env -> KNormal env
        LetRec: {env: Env} -> (f: FunDef env arity ret) -> KNormal (getName f :: env) -> KNormal env
        LetTuple: {env: Env} -> (tup: Vect (2 + k) EnvEntry) -> (y: Id) -> KNormal ((reverse (toList tup)) ++ env) -> KNormal env
        Var: {env: Env} -> (x: Id) -> {auto p: IsKind x Variable} -> KNormal env
        App: {env: Env} -> (x: Id) -> (args:Vect (1 + n) Id) -> KNormal env
        Tuple: {env: Env} -> (xs: Vect (2 + n) Id) -> KNormal env
        Get: {env: Env} -> (x: Id) -> (y: Id) -> KNormal env
        Put: {env: Env} -> (x: Id) -> (y: Id) -> (z: Id) -> KNormal env
        ExtArray: {env: Env} -> (x: Id) -> KNormal env
        ExtFunApp: {env: Env} -> (x: Id) -> (Vect (1 + n) Id) -> KNormal env


    record FunDef (env: Env) (arity: DPair Nat (\n => GT n 0)) (ret: Type) where
        constructor MkFunDef
        name : EnvEntry
        args : Vect (arity.fst) EnvEntry
        body : KNormal ((reverse (toList args)) ++ (name::env))

    getName: FunDef env arity ret -> EnvEntry
    getName (MkFunDef name _ _) = name

    data InRange : Nat -> Nat -> Type where
        IsInRange : (x : Nat) -> (n <= x = True) -> (x <= m = True) -> InRange n m

    Interpolation Id where
        interpolate id = show id

    Interpolation (KNormal env) where
        interpolate e = case e of
            U => "()"
            (I i) => show i
            (Fl f) => show f
            (Neg x) => "(- \{x})"
            (Add x y) => "(\{x} + \{y})"
            (Sub x y) => "(\{x} - \{y})"
            (FNeg x) => "(-. \{x})"
            (FAdd x y) => "(\{x} +. \{y})"
            (FSub x y) => "(\{x} -. \{y})"
            (FMul x y) => "(\{x} *. \{y})"
            (FDiv x y) => "(\{x} /. \{y})"
            (Var x) => show x
            (App x y) => "(\{x} \{joinBy " " (toList (map show y))})"
            (Tuple xs) => "(\{joinBy ", " (toList (map show xs))})"
            (Get x y) => "(\{x}.(\{y}))"
            (Put x y z) => "(\{x}.(\{y}) <- \{z})"
            (Let x t e1 e2) => "(let \{x} => \{e1} in \{e2})"
            (LetTmp x t e1 e2) => "(let \{x} => \{e1} in \{e2})"
            (IfEqi x y e1 e2) => "(if (\{x} = \{y}) then \{e1} else \{e2})"
            (IfLEi x y e1 e2) => "(if (\{x} <= \{y}) then \{e1} else \{e2})"
            (IfEqf x y e1 e2) => "(if (\{x} = \{y}) then \{e1} else \{e2})"
            (IfLEf x y e1 e2) => "(if (\{x} <= \{y}) then \{e1} else \{e2})"
            (LetRec (MkFunDef name args body) e2) => 
                let args = map (show . fst . fst) args in "(let rec \{fst . fst $ name} \{joinBy " " (toList args)} = \{body} in \{e2})"
            (LetTuple xs y e') => "(let (\{joinBy ", " (toList (map (show . fst . fst) xs))}) = \{y} in \{e'})"
            (ExtArray x) => "(extarray \{x})"
            (ExtFunApp x xs) => "(\{x} \{joinBy " " (toList (map show xs))})"

    Show Id where
        show id = id.name

    Show (KNormal env) where
        show e = interpolate e

    fv: KNormal env -> SortedSet Id
    fv e = case e of
        U => SortedSet.empty 
        (I _) => SortedSet.empty
        (Fl _) => SortedSet.empty 
        (ExtArray _) => SortedSet.empty
        (Neg x ) => singleton x
        (FNeg x) => singleton x
        (Var x) => singleton x
        (Add x y) => SortedSet.fromList [x, y]
        (Sub x y) => SortedSet.fromList [x, y]
        (Get x y) => SortedSet.fromList [x, y]
        (FAdd x y) => SortedSet.fromList [x, y]
        (FSub x y) => SortedSet.fromList [x, y]
        (FMul x y) => SortedSet.fromList [x, y]
        (FDiv x y) => SortedSet.fromList [x, y]
        (Put x y z) => SortedSet.fromList [x, y, z]
        (IfEqi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
        (IfLEi x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
        (IfEqf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
        (IfLEf x y e1 e2) => insert x (insert y (union (fv e1) (fv e2)))
        (Let x t e1 e2) => union (fv e1) (delete x (fv e2))
        (LetTmp x t e1 e2) => union (fv e1) (delete x (fv e2))
        (LetRec (MkFunDef name args body) e2) => delete (fst . fst $ name) (union (fv e2) (difference (fv body) (fromList (toList (map (fst . fst) args)))))
        (LetTuple xs y e') => insert y (difference (fv e') (fromList (toList (map (fst . fst) xs))))
        (Tuple xs) => SortedSet.fromList (toList xs)
        (ExtFunApp _ xs) => SortedSet.fromList (toList xs)
        (App x xs) => SortedSet.fromList (x :: (toList xs))

    insert_let: {env: Env} -> (KNormal env, Ty) -> ((x: Id)-> {auto p: (IsKind x Temporary) `Either` (IsKind x Variable)} -> (KNormal env, Ty)) -> (KNormal env, Ty)
    insert_let {env} (Var x, _) k = k x
    insert_let {env} (e, t) k with (MkId (TmpName 42)) proof prf
            insert_let {env} (e, t) k | x = let (e', t') = k x in (LetTmp x t e e', t')

    ||| transform to k-normal form
    g: (env: Env) -> Syntax.Node -> (KNormal env, Ty)
    g _ U = (U, TyUnit)
    g _ (I i) = (I i, TyI32)
    g _ (B b) = (I (if b then 1 else 0), TyI32)
    g _ (F f) = (Fl f, TyF32)
    g env (Not {key} e) = g env (If {key} e (B {key} False) (B {key} True))
    g env (Neg e) = insert_let (g env e) (\x => (Neg x, TyI32))
    g env (Add e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (Add x y, TyI32)))
    g env (Sub e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (Sub x y, TyI32)))
    g env (FNeg e) = insert_let (g env e) (\x => (FNeg x, TyF32))
    g env (FAdd e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (FAdd x y, TyF32)))
    g env (FSub e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (FSub x y, TyF32)))
    g env (FMul e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (FMul x y, TyF32)))
    g env (FDiv e1 e2) = insert_let (g env e1) (\x => insert_let (g env e2) (\y => (FDiv x y, TyF32)))
    g env e@(Eq {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env e@(Neq {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env e@(Lt {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env e@(Le {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env e@(Gt {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env e@(Ge {key} _ _) = g env (If {key} e (B {key} True) (B {key} False))
    g env (If {key} (Not e1) e2 e3) = g env (If {key} e1 e3 e2)
    g env (If {key} (Eq e1 e2) e3 e4) = 
        let (e1', t1) = g env e1 in
        insert_let (e1', t1) (\x => 
            insert_let (g env e2) (\y => 
                let (e3', t) = g env e3 in
                let (e4', _) = g env e4 in
                case t1 of
                    (_ ** TyI32) => (IfEqi x y e3' e4', t)
                    (_ ** TyF32) => (IfEqf x y e3' e4', t)
                    _ impossible))

    -- isLet : KNormal _ -> Bool
    -- isLet (Let _ _ _) = True
    -- isLet _ = False

