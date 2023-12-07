module Assoc

import Control.Function
import Control.Monad.Writer
import Control.Monad.Identity
import KNormal
import Syntax
import Binding
import Data.List
import Info
    
export
g: KNormal a -> Writer (List a -> List a) (KNormal a)
g (IfFalse {key} x e1 e2) = IfFalse {key} x <$> (g e1) <*> (g e2)
g (IfEq {key, t} x y e1 e2) = IfEq {key, t} x y <$> (g e1) <*> (g e2)
-- g (IfEqf {key} x y e1 e2) = IfEqf {key, t} x y <$> (g e1) <*> (g e2)
g (IfLE {key, t} x y e1 e2) = IfLE {key, t} x y <$> (g e1) <*> (g e2)
-- g (IfLEf {key} x y e1 e2) = IfLEf {key} x y <$> (g e1) <*> (g e2)
g (Let {key} x t e1 e2) = insert False !(g e1) 
where 
    insert: Bool -> KNormal a -> Writer (List a -> List a) (KNormal a)
    insert _ (Let {key} y yt e3 e4) = Let {key} y yt e3 <$> (insert True e4)
    insert _ (LetTmp {key} y yt e3 e4) = LetTmp {key} y yt e3 <$> (insert True e4)
    insert _ (LetRec {key} f e) = LetRec {key} f <$> (insert True e)
    insert _ (LetTuple {key} yts z e) = LetTuple {key} yts z <$> (insert True e)
    insert flag e = do when flag (tell (key::)); e2 <- g e2; pure $ Let {key} x t e e2 -- (changeEnv ((x, t)::env') e2)
g (LetTmp {key} x t e1 e2) = insert' False !(g e1)
where 
    insert': Bool -> KNormal a -> Writer (List a -> List a) (KNormal a)
    insert' _ (Let {key} y yt e3 e4) = Let {key} y yt e3 <$> (insert' True e4)
    insert' _ (LetTmp {key} y yt e3 e4) = LetTmp {key} y yt e3 <$> (insert' True e4)
    insert' _ (LetRec {key} f e) = LetRec {key} f <$> (insert' True e)
    insert' _ (LetTuple {key} yts z e) = LetTuple {key} yts z <$> (insert' True e)
    insert' flag e = do when flag (tell (key::)); e2 <- g e2; pure $ LetTmp {key} x t e e2 -- (changeEnv env' e2)
g (LetRec {key} (MkFunDef name args body) e2) = LetRec {key} (MkFunDef name args !(g body)) <$> (g e2)
g (LetTuple {key} xts y e) = LetTuple {key} xts y <$> (g e)
g e = pure e

export
f: KNormal a -> (List a, KNormal a)
f e = let (e, w) = runIdentity $ runWriterT (g e) in (w [], e)