module Ty

import Data.Vect
import Data.String
import Decidable.Equality


toTupleType: Vect (S n) Type -> Type
toTupleType [x] = x
toTupleType (x::x'::xs) = (x, toTupleType (x::xs))


-- public export
-- data Ty : Type -> Type where
--     TyI32: Ty Int
--     TyF32: Ty Double
--     TyUnit: Ty ()
--     TyBool: Ty Bool
--     TyTuple: {n: Nat} -> (ts: Vect (2 + n) (t: Type ** Ty t)) -> Ty (HVect (map DPair.fst ts))
--     TyArray: (a: (t: Type ** Ty t)) -> Ty (List (fst a)) 
--     TyFun: {n: Nat} -> (ts: Vect (1 + n) (t: Type ** Ty t)) -> (b: Type ** Ty b) -> Ty (Fun (map DPair.fst ts) b)

public export
data Ty : Type where
    TyI32: Ty
    TyF32: Ty
    TyUnit: Ty
    TyBool: Ty
    TyTuple: {n: Nat} -> (ts: Vect (2 + n) Ty) -> Ty
    TyArray: (a: Ty) -> Ty 
    TyFun: (a: Ty) -> (b: Ty) -> Ty

export
Eq Ty where
    (==) TyI32 TyI32 = True
    (==) TyF32 TyF32 = True
    (==) TyUnit TyUnit = True
    (==) TyBool TyBool = True
    (==) (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) with (decEq n1 n2)
        (==) (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) | Yes p = let ys' = rewrite p in ys in assert_total (==) xs ys'
        (==) (TyTuple xs) (TyTuple ys) | No _ = False
    (==) (TyArray a) (TyArray b) = a == b
    (==) (TyFun a b) (TyFun c d) = a == c && b == d
    (==) _ _ = False

    (/=) t1 t2 = not (t1 == t2)

export
Show Ty where 
    show TyI32 = "int"
    show TyF32 = "float"
    show TyUnit = "unit"
    show TyBool = "bool"
    show (TyTuple xs) = "(" ++ (" * " `joinBy` (assert_total show <$> toList xs)) ++ ")"
    show (TyArray a) = "(" ++ show a ++ " array)"
    -- show (TyFun xs x) = "(" ++ (" -> " `joinBy` (assert_total show <$> toList xs)) ++ " -> " ++ show x ++ ")"
    show (TyFun a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"

public export 
data IsNumTy: Ty -> Type where
    TyI32IsNum: IsNumTy TyI32
    TyF32IsNum: IsNumTy TyF32

public export
data IsEqTy: Ty -> Type where
    TyI32IsEq: IsEqTy TyI32
    TyF32IsEq: IsEqTy TyF32
    -- TyUnitIsEq: IsEqTy TyUnit
    TyBoolIsEq: IsEqTy TyBool

Injective TyArray where
    injective Refl = Refl

Biinjective TyFun where 
    biinjective Refl = (Refl, Refl)

export
lemma: (TyTuple {n=n1'} xs = TyTuple {n=n2'} ys) -> (n1' = n2', xs = ys)
lemma Refl = (Refl, Refl)

lemma': {xs: Vect (2 + n1) Ty} -> {ys: Vect (2 + n2) Ty} -> (p: n1 = n2) -> (xs = (rewrite p in ys)) -> (TyTuple {n=n1} xs = TyTuple {n=n2} ys)
lemma' Refl Refl = Refl

-- lemma2': {xs: Vect (1 + n1) Ty} -> {ys: Vect (1 + n2) Ty} -> {x, y: Ty} -> (p: n1 = n2) -> (xs = (rewrite p in ys)) -> (x = y) -> (TyFun {n=n1} xs x = TyFun {n=n2} ys y)
-- lemma2' Refl Refl Refl = Refl
-- maybeEq: (a, b: Ty) -> Maybe (a = b)
-- maybeEq TyI32 TyI32 = Just Refl
-- maybeEq TyF32 TyF32 = Just Refl
-- maybeEq TyUnit TyUnit = Just Refl
-- maybeEq TyBool TyBool = Just Refl
-- maybeEq (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) with (decEq n1 n2)
--     maybeEq (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) | Yes p = 
--         traverse (\(x, y) => maybeEq x y) (zip xs (rewrite p in ys)) >>= \p' => Just (lemma' p p')
--     maybeEq (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) | No _ = Nothing
-- maybeEq (TyArray a) (TyArray b) = cong TyArray <$> maybeEq a b
-- maybeEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) with (decEq n1 n2)
--     maybeEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) | Yes p = 
--         foldlM (\(n ** acc), (x, y) => do p <- maybeEq x y; pure (S n ** cong2 (Vect.(::)) p acc)) 
--         (0 ** Refl) 
--         (zip xs (rewrite p in ys)) >>= \(_ ** p'):(xs=(rewrite p in ys)) => do
--             p'' <- maybeEq x y
--             pure (lemma' p p' ** p'')
--     maybeEq (TyFun xs x) (TyFun ys y) | No _ = Nothing

-- maybeEq _ _ = Nothing

-- reflNotNothing: (a: Ty) -> Not (maybeEq a a = Nothing)
-- reflNotNothing TyI32 Refl impossible
-- reflNotNothing TyF32 Refl impossible
-- reflNotNothing TyUnit Refl impossible
-- reflNotNothing TyBool Refl impossible
-- reflNotNothing (TyTuple _) Refl impossible
-- reflNotNothing (TyArray _) Refl impossible
-- reflNotNothing (TyFun _ _) Refl impossible

export
DecEq Ty where 
    decEq TyI32 TyI32 = Yes Refl
    decEq TyF32 TyF32 = Yes Refl
    decEq TyUnit TyUnit = Yes Refl
    decEq TyBool TyBool = Yes Refl
    decEq (TyTuple {n=n1} (x::x'::xs)) (TyTuple {n=n2} (y::y'::ys)) with (decEq n1 n2)
        decEq (TyTuple (x::x'::xs)) (TyTuple (y::y'::ys)) | No contra = No (\k => let (a, _) = lemma k in contra a)
        decEq (TyTuple {n=n1} (x::x'::xs)) (TyTuple {n=n2} (y::y'::ys)) | Yes p with (decEq (x::x'::xs) (rewrite p in y::y'::ys))
            decEq (TyTuple {n=n1} (x::x'::xs)) (TyTuple {n=n2} (y::y'::ys)) | Yes p | Yes p' = Yes (lemma' p p')
            decEq (TyTuple {n=n1} (x::x'::xs)) (TyTuple {n=n2} (y::y'::ys)) | Yes p | No contra = No believe_me

    decEq (TyArray a) (TyArray b) = decEqCong $ decEq a b
    decEq (TyFun a b) (TyFun c d) = decEqCong2 (decEq a c) (decEq b d)
    -- decEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) with (decEq n1 n2)
    --     decEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) | Yes p with (decEq xs (rewrite p in ys)) | (decEq x y)
    --         decEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) | Yes p | Yes p' | Yes p'' = Yes (lemma2' p p' p'')
    --         decEq (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) | Yes p | _ | _ = No believe_me
    --     decEq (TyFun xs x) (TyFun ys y) | No _ = No believe_me
    decEq _ _ = No believe_me
