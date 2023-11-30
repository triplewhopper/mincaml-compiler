module Closure

import Binding
import Utils
import Data.List
import Data.List1
import Data.Vect
import Data.String
import Data.Maybe
import Data.SortedSet
import Data.SortedMap
import KNormal
import Control.Monad.RWS
import Control.Monad.Identity

mutual
    public export
    record Closure (a: Type) (n: Nat) where 
        constructor Cls
        entry: Label
        -- locals: List1 Id
        actualFv: Vect n (IdName Variable)
        -- body: Exp a
    public export
    data Exp: Type -> Type where
        U: {key: a} -> Exp a
        B: {key: a} -> Bool -> Exp a
        I: {key: a} -> Int -> Exp a
        Fl: {key: a} -> Double -> Exp a
        Var: {key: a} -> IdName Variable -> Exp a
        Get: {key: a} -> Id -> Id -> Exp a
        Neg: {key: a} -> Id -> Exp a
        FNeg: {key: a} -> Id -> Exp a
        AppDir: {key: a} -> {n: Nat} -> Label -> Vect (S n) Id -> Exp a
        AppCls: {key: a} -> {n: Nat} -> Id -> Vect (S n) Id -> Exp a
        ExtArray: {key: a} -> Label -> Exp a
        FMul: {key: a} -> Id -> Id -> Exp a
        FDiv: {key: a} -> Id -> Id -> Exp a
        FAdd: {key: a} -> Id -> Id -> Exp a
        FSub: {key: a} -> Id -> Id -> Exp a
        Add: {key: a} -> Id -> Id -> Exp a
        Sub: {key: a} -> Id -> Id -> Exp a
        Tuple: {key: a} -> {n: Nat} -> Vect (S (S n)) Id -> Exp a
        Put: {key: a} -> Id -> Id -> Id -> Exp a
        IfFalse: {key: a} -> Id -> Exp a -> Exp a -> Exp a
        IfEqi: {key: a} -> Id -> Id -> Exp a -> Exp a -> Exp a
        IfEqf: {key: a} -> Id -> Id -> Exp a -> Exp a -> Exp a
        IfLEi: {key: a} -> Id -> Id -> Exp a -> Exp a -> Exp a
        IfLEf: {key: a} -> Id -> Id -> Exp a -> Exp a -> Exp a
        Let: {key: a} -> IdName Variable -> Ty -> Exp a -> Exp a -> Exp a
        LetTmp: {key: a} -> IdName Temporary -> Ty -> Exp a -> Exp a -> Exp a
        MakeCls: {key: a} -> {n: Nat} -> Binding -> Closure a n -> Exp a -> Exp a
        LetTuple: {key: a} -> {n: Nat} -> Vect (S (S n)) Binding -> Id -> Exp a -> Exp a

    public export
    record FunDef (a: Type) (arity': Nat) where
        constructor MkFunDef
        name: Binding
        args: Vect (S arity') Binding
        formalFv: List Binding
        body: Exp a

public export
data Program: Type -> Type where 
    Prog: List (arity': Nat ** FunDef a arity') -> Exp a -> Program a

filter': Vect n Id -> SortedSet (IdName Variable)
filter' xs = fromList (foldl (\acc, x => case x of (MkId x@(VarName _ _)) => x::acc; (MkId x@(ExtName _)) => x::acc; _ => acc) [] xs)

singleton': Id -> SortedSet (IdName Variable)
singleton' (MkId x@(VarName _ _)) = singleton x
singleton' (MkId x@(ExtName _)) = singleton x
singleton' _ = empty

insert': Id -> SortedSet (IdName Variable) -> SortedSet (IdName Variable)
insert' (MkId x@(VarName _ _)) xs = insert x xs
insert' (MkId x@(ExtName _)) xs = insert x xs
insert' _ xs = xs

fv: Exp a -> SortedSet (IdName Variable)
fv U = empty
fv (B _) = empty
fv (I _) = empty
fv (Fl _) = empty
fv (Var x) = singleton x
fv (Get x y) = filter' [x, y]
fv (Neg x) = singleton' x
fv (FNeg x) = singleton' x
fv (AppDir _ xs) = filter' xs
fv (AppCls x xs) = filter' (x::xs)
fv (ExtArray _) = empty
fv (FMul x y) = filter' [x, y]
fv (FDiv x y) = filter' [x, y]
fv (FAdd x y) = filter' [x, y]
fv (FSub x y) = filter' [x, y]
fv (Add x y) = filter' [x, y]
fv (Sub x y) = filter' [x, y]
fv (Tuple xs) = filter' xs
fv (Put x y z) = filter' [x, y, z]
fv (IfFalse x e1 e2) = insert' x (union (fv e1) (fv e2))
fv (IfEqi x y e1 e2) = insert' x (insert' y (union (fv e1) (fv e2)))
fv (IfEqf x y e1 e2) = insert' x (insert' y (union (fv e1) (fv e2)))
fv (IfLEi x y e1 e2) = insert' x (insert' y (union (fv e1) (fv e2)))
fv (IfLEf x y e1 e2) = insert' x (insert' y (union (fv e1) (fv e2)))
fv (Let x _ e1 e2) = union (fv e1) (delete x (fv e2))
fv (LetTmp _ _ e1 e2) = union (fv e1) (fv e2)
fv (MakeCls (x, _) (Cls entry actualFv) e) = delete x (union (fromList (toList actualFv)) (fv e))
fv (LetTuple xs y e) = insert' y (difference (fv e) (fromList (toList (fst <$> xs))))

-- Show a => Show (Closure a n) where
--     show (Cls entry actualFv) = "Cls " ++ show entry ++ " " ++ show actualFv

g: SortedSet (IdName Variable) -> KNormal a env -> RWS (SortedMap (IdName Variable) Ty) () (List (n: Nat ** FunDef a n)) (Exp a)
g _ (U {key}) = pure (U {key})
g _ (B {key} b) = pure (B {key} b)
g _ (I {key} i) = pure (I {key} i)
g _ (Fl {key} f) = pure (Fl {key} f)
g _ (Var {key} x) = pure (Var {key} x)
g _ (Get {key} x y) = pure (Get {key} x y)
g _ (Neg {key} x) = pure (Neg {key} x)
g _ (FNeg {key} x) = pure (FNeg {key} x)
g known (App {key} {p} x ys) with (x)
    g known (App {key} {p} x ys) | (VarName _ _) = if contains x known then info "directly applying \{x}" pure (AppDir {key} (MkLabel x) ys) else pure (AppCls {key} (MkId x) ys)
    g known (App {key} {p} x ys) | (ExtName _) impossible
g _ (AppTmp {key} x ys) = pure $ AppCls {key} (MkId x) ys
g _ (ExtArray {key} x) = pure (ExtArray {key} (MkLabel (ExtName x)))
g _ (ExtFunApp {key} x ys) = pure (AppDir {key} (MkLabel (ExtName x)) ys)
g _ (FMul {key} x y) = pure (FMul {key} x y)
g _ (FDiv {key} x y) = pure (FDiv {key} x y)
g _ (FAdd {key} x y) = pure (FAdd {key} x y)
g _ (FSub {key} x y) = pure (FSub {key} x y)
g _ (Add {key} x y) = pure (Add {key} x y)
g _ (Sub {key} x y) = pure (Sub {key} x y)
g _ (Tuple {key} xs) = pure (Tuple {key} xs)
g _ (Put {key} x y z) = pure (Put {key} x y z)
g known (IfFalse {key} x e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (IfFalse {key} x e1' e2')
g known (IfEqi {key} x y e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (IfEqi {key} x y e1' e2')
g known (IfEqf {key} x y e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (IfEqf {key} x y e1' e2')
g known (IfLEi {key} x y e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (IfLEi {key} x y e1' e2')
g known (IfLEf {key} x y e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (IfLEf {key} x y e1' e2')
g known (Let {key} x t e1 e2) = do
    e1' <- g known e1
    e2' <- local (insert x t) (g known e2)
    pure (Let {key} x t e1' e2')
g known (LetTmp {key} x t e1 e2) = do
    e1' <- g known e1
    e2' <- g known e2
    pure (LetTmp {key} x t e1' e2')
g known (LetRec {key} (MkFunDef (x, t) args e1) e2) = do
    backup <- get
    let known' = insert x known
    e1' <- local (insertFrom ((x, t)::args)) (g known' e1)
    let zs = difference (fv e1') (fromList (toList (fst <$> args)))
    (known', e1') <-
        if zs /= empty then do
            info "free variable(s) \{joinBy ", " (show <$> SortedSet.toList zs)} found in function `\{x}`." pure ()
            info "function \{x} cannot be directly applied in fact." pure ()
            put backup
            e1' <- local (insertFrom ((x, t)::args)) (g known e1)
            pure (known, e1')
        else do
            pure (known', e1')
    let zs: SortedSet (IdName Variable) = difference (fv e1') (fromList (x :: toList (fst <$> args)))
    zts <- asks (\env => (\z => (z, SortedMap.lookup z env)) <$> SortedSet.toList zs)
    let zts: List Binding = foldl (\acc, (z, t) => case t of 
            Nothing => warn "in Closure.g, collecting free vars for function `\{x}` of type `\{show t}`: \{z} has no type!!!!" acc
            Just t => (z, t)::acc) [] zts
    modify (\toplevel => Prelude.(::) (_ ** MkFunDef (x, t) args zts e1') toplevel)
    e2' <- local (insert x t) (g known' e2)
    if contains x (fv e2') then
        pure (MakeCls {key} (x, t) (Cls (MkLabel x) (fromList $ fst <$> zts)) e2')
        else info "eliminating closure \{x}" pure e2'

g known (LetTuple {key} xs y e) = do
    e' <- local (insertFrom xs) (g known e)
    pure (LetTuple {key} xs y e')

f: KNormal a env -> Program a
f e = let (e', toplevel, ()) = runRWS empty [] (g empty e) in Prog (reverse toplevel) e'