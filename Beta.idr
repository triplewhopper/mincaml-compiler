module Beta 

import Id
import Data.List
import Data.Vect
import Data.Maybe
import Data.SortedMap
import Control.Monad.State
import KNormal 
import Utils
import Ty

||| Id Union Find
0 IdUf: Type
IdUf = SortedMap Id (IdName Variable)

find1: IdName Variable -> State IdUf (IdName Variable)
find1 x = let x' = MkId x in case lookup x' !get of
  Just y => if x == y then pure y else do fy <- find1 y; modify (insert x' fy); pure fy
  Nothing => pure x

find2: (x: Id) -> State IdUf Id 
find2 x = case lookup x !get of
  Just y => let y' = MkId y in if x == y' then pure y' else do fy <- find1 y ; modify (insert x fy); pure y'
  Nothing => pure x

g: KNormal a env -> State IdUf (KNormal a env)
g e@U = pure e
g e@(B _) = pure e
g e@(I _) = pure e
g e@(Fl _) = pure e
g (Var x {key}) = Var {key} <$> (find1 x)
g (Get x y {key}) = Get {key} <$> (find2 x) <*> (find2 y)
g (Neg x {key}) = Neg {key} <$> (find2 x)
g (FNeg x {key}) = FNeg {key} <$> (find2 x)
g (App x ys {key}) = (\x, ys => App {key} x ys) <$> (find2 x) <*> (traverse find2 ys)
g (ExtArray x {key}) = pure (ExtArray {key} x)
g (ExtFunApp x ys {key}) = ExtFunApp {key} x <$> (traverse find2 ys)
g (FMul x y {key}) = FMul {key} <$> (find2 x) <*> (find2 y)
g (FDiv x y {key}) = FDiv {key} <$> (find2 x) <*> (find2 y)
g (FAdd x y {key}) = FAdd {key} <$> (find2 x) <*> (find2 y)
g (FSub x y {key}) = FSub {key} <$> (find2 x) <*> (find2 y)
g (Add x y {key}) = Add {key} <$> (find2 x) <*> (find2 y)
g (Sub x y {key}) = Sub {key} <$> (find2 x) <*> (find2 y)
g (Tuple xs {key}) = Tuple {key} <$> (traverse find2 xs)
g (Put x y z {key}) = Put {key} <$> (find2 x) <*> (find2 y) <*> (find2 z)
g (IfFalse x e1 e2 {key}) = IfFalse {key} <$> (find2 x) <*> (g e1) <*> (g e2)
g (IfEqi x y e1 e2 {key}) = IfEqi {key} <$> (find2 x) <*> (find2 y) <*> (g e1) <*> (g e2)
g (IfLEi x y e1 e2 {key}) = IfLEi {key} <$> (find2 x) <*> (find2 y) <*> (g e1) <*> (g e2)
g (IfEqf x y e1 e2 {key}) = IfEqf {key} <$> (find2 x) <*> (find2 y) <*> (g e1) <*> (g e2)
g (IfLEf x y e1 e2 {key}) = IfLEf {key} <$> (find2 x) <*> (find2 y) <*> (g e1) <*> (g e2)
g (Let x t e1 e2 {key}) = do
  e1 <- g e1
  case e1 of
    Var y => do
      fy <- find1 y
      if y == fy then info "beta-reducing \{x} = \{y}" modify (insert (MkId x) y)
        else info "beta-reducing \{x} = \{y} (aka. \{fy})" modify (insert (MkId x) fy)
      g (changeEnv env e2)
    _ => do
      e2 <- g e2
      pure (Let {key} x t e1 e2)
g (LetTmp x t e1 e2 {key}) = do
  e1 <- g e1
  case e1 of
    Var y => do
      fy <- find1 y
      if y == fy then info "beta-reducing \{x} = \{y}" modify (insert (MkId x) y)
        else info "beta-reducing \{x} = \{y} (aka. \{fy})" modify (insert (MkId x) fy)
      g e2
    _ => do
      e2 <- g e2
      pure (LetTmp {key} x t e1 e2)
g (LetRec (MkFunDef f xs e1) e2 {key}) = do
    e1 <- g e1
    e2 <- g e2
    pure (LetRec {key} (MkFunDef f xs e1) e2)
g (LetTuple xs y e {key}) = LetTuple {key} xs <$> (find2 y) <*> (g e)

export 
f: KNormal a env -> KNormal a env
f e = evalState empty (g e)