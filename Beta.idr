module Beta 

import Binding
import Data.List
import Data.Maybe
import Data.SortedMap
import Control.Monad.State
import Control.Monad.Writer
import KNormal 
import Utils

||| Id Union Find
0 IdUf: Type
IdUf = SortedMap Id (IdName Variable)

0 WS: Type -> Type -> Type
WS a = WriterT (List a -> List a) (State IdUf)

find1: IdName Variable -> WS a (IdName Variable)
find1 x = let x' = MkId x in case lookup x' !(lift get) of
  Just y => if x == y then pure y else do fy <- find1 y; lift $ modify (insert x' fy); pure fy
  Nothing => pure x

find2: IdName Temporary -> WS a (Maybe (IdName Variable)) 
find2 x = let x' = MkId x in case lookup x' !(lift get) of
  Just y => do fy <- find1 y; lift $ modify (insert x' fy); pure (Just fy)
  Nothing => pure Nothing

find3: (x: Id) -> WS a Id 
find3 x = case lookup x !(lift get) of
  Just y => let y' = MkId y in if x == y' then pure y' else do fy <- find1 y ; lift $ modify (insert x fy); pure y'
  Nothing => pure x

tellWhenNeq: (Eq b) => a -> (x: b) -> (x': WS a b) -> (WS a (b -> KNormal a)) -> WS a (KNormal a)
tellWhenNeq key x x' f = do x' <- x'; when (x /= x') (tell (key::)); pure $ !f x'

tellWhenNeq2: (Eq b, Eq c) => a -> b -> c -> WS a b -> WS a c -> (WS a (b -> c -> KNormal a)) -> WS a (KNormal a)
tellWhenNeq2 key x y x' y' f = do x' <- x'; y' <- y'; when (x /= x' || y /= y') (tell (key::)); pure $ !f x' y'

g: KNormal a -> WS a (KNormal a)
g e@U = pure e
g e@(B _) = pure e
g e@(I _) = pure e
g e@(Fl _) = pure e
g (Var x {key, t}) = tellWhenNeq key x (find1 x) (pure $ \x => Var x {key, t})
g (Get x y {key, t}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ \x, y => Get x y {key, t})
g (Neg x {key, t}) = tellWhenNeq key x (find3 x) (pure $ \x => Neg x {key, t}) 
-- g (FNeg x {key}) = tellWhenNeq key x (find3 x) (pure $ FNeg {key}) 
g (App x y {key, argty, retty}) = tellWhenNeq2 key x y (find1 x) (find3 y) (pure f)
where 
  f: IdName Variable -> Id -> KNormal a
  f x@(VarName _ _) y = App x y {key, argty, retty}
  f (ExtName x') y = ExtFunApp x' y {key, argty, retty}
-- g (App x ys {key}) = tellWhenNeq2 key x ys (find1 x) (traverse find3 ys) (pure f)
  -- f: {n: Nat} -> IdName Variable -> Vect (1 + n) Id -> KNormal a env
  -- f x@(VarName _ _) ys = App x ys {key}
  -- f (ExtName x') ys = ExtFunApp x' ys {key}
g (AppTmp x y {key, argty, retty}) = do 
  x' <- find2 x
  y' <- find3 y
  case x' of 
    Nothing => do when (y' /= y) (tell (key::)); pure $ AppTmp x y' {key, argty, retty}
    Just x' => do tell (key::); pure $ f x' y'
where 
  f: IdName Variable -> Id -> KNormal a
  f x@(VarName _ _) y = App x y {key, argty, retty}
  f (ExtName x') y = ExtFunApp x' y {key, argty, retty}
-- g (AppTmp x ys {key}) = do 
--   x' <- find2 x
--   ys' <- traverse find3 ys
--   case x' of 
--     Nothing => do when (ys' /= ys) (tell (key::)); pure $ AppTmp x {key} ys'
--     Just x' => do tell (key::); pure $ f x' ys'
-- where 
--   f: {n: Nat} -> IdName Variable -> Vect (1 + n) Id -> KNormal a env
--   f x@(VarName _ _) ys = App x ys {key}
--   f (ExtName x') ys = ExtFunApp x' ys {key}
g (ExtArray x {key}) = pure (ExtArray {key} x)
-- g (ExtFunApp x ys {key}) = tellWhenNeq key ys (traverse find3 ys) (pure $ ExtFunApp {key} x)
g (ExtFunApp x y {key, argty, retty}) = tellWhenNeq key y (find3 y) (pure $ \y => ExtFunApp {key, argty, retty} x y)
g (BinaryOp op x y {key, t}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ \x, y => BinaryOp op x y {key, t})
-- g (FMul x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ FMul {key})
-- g (FDiv x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ FDiv {key})
-- g (FAdd x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ FAdd {key})
-- g (FSub x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ FSub {key})
-- g (Add x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ Add {key})
-- g (Sub x y {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (pure $ Sub {key})
g (Tuple xs {key, ts}) = tellWhenNeq key xs (traverse find3 xs) (pure $ \xs => Tuple xs {key, ts})
g (Put x y z {key, tz}) = (\x, y, z => Put x y z {key, tz}) <$> (find3 x) <*> (find3 y) <*> (find3 z)
g (IfFalse x e1 e2 {key}) = tellWhenNeq key x (find3 x) (do e1 <- g e1; e2 <- g e2; pure $ (\x => IfFalse {key} x e1 e2))
g (IfEq x y e1 e2 {key, t}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfEq {key, t} x y e1 e2))
g (IfLE x y e1 e2 {key, t}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfLE {key, t} x y e1 e2))
-- g (IfEqi x y e1 e2 {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfEqi {key} x y e1 e2))
-- g (IfLEi x y e1 e2 {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfLEi {key} x y e1 e2))
-- g (IfEqf x y e1 e2 {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfEqf {key} x y e1 e2))
-- g (IfLEf x y e1 e2 {key}) = tellWhenNeq2 key x y (find3 x) (find3 y) (do e1 <- g e1; e2 <- g e2; pure $ (\x, y => IfLEf {key} x y e1 e2))
g (Let x t e1 e2 {key}) = do
  e1 <- g e1
  case e1 of
    Var y => do
      fy <- find1 y
      if y == fy then info "beta-reducing \{x} = \{y}" lift $ modify (insert (MkId x) y)
        else info "beta-reducing \{x} = \{y} (aka. \{fy})" lift $ modify (insert (MkId x) fy)
      tell (key::)
      g e2
      -- g (changeEnv env e2)
    _ => do
      e2 <- g e2
      pure (Let {key} x t e1 e2)
g (LetTmp x t e1 e2 {key}) = do
  e1 <- g e1
  case e1 of
    Var y => do
      fy <- find1 y
      if y == fy then info "beta-reducing \{x} = \{y}" lift $ modify (insert (MkId x) y)
        else info "beta-reducing \{x} = \{y} (aka. \{fy})" lift $ modify (insert (MkId x) fy)
      tell (key::)
      g e2
    _ => do
      e2 <- g e2
      pure (LetTmp {key} x t e1 e2)
g (LetRec (MkFunDef f xs e1) e2 {key}) = do
    e1 <- g e1
    e2 <- g e2
    pure (LetRec {key} (MkFunDef f xs e1) e2)
g (LetTuple xs y e {key}) = tellWhenNeq key y (find3 y) (do e <- g e; pure $ (\y => LetTuple {key} xs y e))

export 
f: KNormal a -> (List a, KNormal a)
f e = do 
  let (e, w) = evalState empty (runWriterT (g e))
  (w [], e)
