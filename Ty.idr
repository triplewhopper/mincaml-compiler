module Ty

import Data.Vect
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
    TyFun: {n: Nat} -> (ts: Vect (1 + n) Ty) -> (b: Ty) -> Ty

Eq Ty where
    (==) TyI32 TyI32 = True
    (==) TyF32 TyF32 = True
    (==) TyUnit TyUnit = True
    (==) TyBool TyBool = True
    (==) (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) with (decEq n1 n2)
        (==) (TyTuple {n=n1} xs) (TyTuple {n=n2} ys) | Yes p = let ys' = rewrite p in ys in assert_total (==) xs ys'
        (==) (TyTuple xs) (TyTuple ys) | No _ = False
    (==) (TyArray a) (TyArray b) = a == b
    (==) (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) with (decEq n1 n2)
        (==) (TyFun {n=n1} xs x) (TyFun {n=n2} ys y) | Yes p = let ys' = rewrite p in ys in x == y && assert_total (==) xs ys'
        (==) (TyFun xs x) (TyFun ys y) | No _ = False
    (==) _ _ = False

    (/=) t1 t2 = not (t1 == t2)

public export
data TypeVar: Type where
    TyVar: Nat -> TypeVar

public export
Eq TypeVar where
    (==) (TyVar n1) (TyVar n2) = n1 == n2

    (/=) (TyVar n1) (TyVar n2) = n1 /= n2

public export
Ord TypeVar where
    compare (TyVar n1) (TyVar n2) = compare n1 n2

Injective TyVar where
    injective Refl = Refl

public export 
DecEq TypeVar where
    decEq (TyVar n1) (TyVar n2) = decEqCong $ decEq n1 n2

export 
Show TypeVar where
    show (TyVar n) = "'t" ++ show n
export
Interpolation TypeVar where
    interpolate (TyVar n) = "'t" ++ show n
-- EqVect: Eq a => {n: Nat} -> (xs: Vect (S n) a) -> (ys: Vect (S n) a) -> Bool
-- EqVect [x] [y] = x == y
-- EqVect (x::x'::xs) (y::y'::ys) = x == y && EqVect (x'::xs) (y'::ys)

-- Eq (t: Type ** Ty t) where
--     (==) (_ ** TyI32) (_ ** TyI32) = True
--     (==) (_ ** TyF32) (_ ** TyF32) = True
--     (==) (_ ** TyUnit) (_ ** TyUnit) = True
--     (==) (_ ** TyBool) (_ ** TyBool) = True
--     (==) (_ ** TyTuple {n=n1} xs) (_ ** TyTuple {n=n2} ys) with (decEq n1 n2)
--         (==) (_ ** TyTuple {n=n1} xs) (_ ** TyTuple {n=n2} ys) | Yes p = let ys' = rewrite p in ys in assert_total EqVect xs ys'
--         (==) (_ ** TyTuple xs) (_ ** TyTuple ys) | No _ = False
--     (==) (_ ** TyArray a) (_ ** TyArray b) = a == b
--     (==) (_ ** TyFun {n=n1} xs x) (_ ** TyFun {n=n2} ys y) with (decEq n1 n2)
--         (==) (_ ** TyFun {n=n1} xs x) (_ ** TyFun {n=n2} ys y) | Yes p = let ys' = rewrite p in ys in x == y && assert_total EqVect xs ys'
--         (==) (_ ** TyFun xs x) (_ ** TyFun ys y) | No _ = False
--     (==) _ _ = False

--     (/=) t1 t2 = not (t1 == t2)

-- interface HasTy (t: Type) where
--     ty: t' -> {auto p: t = t'} -> Ty t

-- HasTy Int where
--     ty _ = TyI32

-- HasTy Double where
--     ty _ = TyF32

-- HasTy () where
--     ty _ = TyUnit

-- HasTy Bool where
--     ty _ = TyBool

-- interface HasTys (k: Nat) (ts: Vect (2 + k) Type) where
--     tys: (ts':Vect (2 + k) Type) -> {auto p: ts'=ts} -> Vect (2 + k) (t: Type ** Ty t)

-- {t1, t2: Type} -> (HasTy t1, HasTy t2) => HasTys 0 [t1, t2] where
--     tys _ = (t1 ** _)::(t2 ** _)::Nil

-- {t: Type} -> {len: Nat} -> {ts: Vect (S(S len)) Type} -> (HasTy t, HasTys len ts) => HasTys (S len) (t::ts) where
--     tys _ = (t ** _):: (tys ts)

-- {n': Nat} -> {ts: Vect (S (S n')) Type} -> (HasTys n' ts) => HasTy (HVect ts) where
--     ty _ = TyTuple (tys ?ts)
    
-- Lemma0: {n: Nat} -> {ts: Vect (S (S n)) Type} -> (HasTys n ts) => (ts = map DPair.fst (tys ts))
-- Lemma0 {n=0} {ts} = ?jk

-- Lemma1: {n1: Nat} -> {n2: Nat} -> (xs: Vect (2 + n1) a) -> (ys: Vect (2 + n2) a) -> (2 + n1 = length xs) -> (2 + n2 = length ys) -> (length xs = length ys) -> n1 = n2
-- Lemma1 xs ys prf prf' prf'' = plusLeftCancel 2 n1 n2 $ trans (trans prf prf'') (sym prf') 
-- -- rewrite plusLeftCancel (2 + n1) (2 + n2) prf'''' in prf''' 

-- Lemma2: (xs : Vect (S (S n2)) (t : Type ** Ty t)) -> (h : n1 = n2) -> Vect (S (S n1)) (t : Type ** Ty t)
-- Lemma2 xs h = rewrite h in xs

-- Lemma3: (xs: Vect (S (S n)) (t: Type ** Ty t)) -> 
--     (ys: Vect (S (S n)) (t: Type ** Ty t)) -> 
--     (h: xs = ys) -> ((TyTuple xs) = (rewrite h in (TyTuple ys)))
-- Lemma3 xs ys p = rewrite p in Refl