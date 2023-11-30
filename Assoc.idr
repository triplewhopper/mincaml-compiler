module Assoc

import Control.Function
import KNormal
import Syntax
import Id
import Ty
import Data.Vect
import Data.List
import Info
    
export
f: KNormal a env -> KNormal a env
f (IfFalse {key} x e1 e2) = IfFalse {key} x (f e1) (f e2)
f (IfEqi {key} x y e1 e2) = IfEqi {key} x y (f e1) (f e2)
f (IfEqf {key} x y e1 e2) = IfEqf {key} x y (f e1) (f e2)
f (IfLEi {key} x y e1 e2) = IfLEi {key} x y (f e1) (f e2)
f (IfLEf {key} x y e1 e2) = IfLEf {key} x y (f e1) (f e2)
f (Let {key} x t e1 e2) = insert (f e1)
where 
    insert: {env': Env} -> KNormal a env' -> KNormal a env'
    insert (Let {key} y yt e3 e4) = Let {key} y yt e3 (insert e4)
    insert (LetTmp {key} y yt e3 e4) = LetTmp {key} y yt e3 (insert e4)
    insert (LetRec {key} f e) = LetRec {key} f (insert e)
    insert (LetTuple {key} yts z e) = LetTuple {key} yts z (insert e)
    insert e = Let {key} x t e (changeEnv ((x, t)::env') (f e2))
f (LetTmp {key} x t e1 e2) = insert' (f e1)
where 
    insert': {env': Env} -> KNormal a env' -> KNormal a env'
    insert' (Let {key} y yt e3 e4) = Let {key} y yt e3 (insert' e4)
    insert' (LetTmp {key} y yt e3 e4) = LetTmp {key} y yt e3 (insert' e4)
    insert' (LetRec {key} f e) = LetRec {key} f (insert' e)
    insert' (LetTuple {key} yts z e) = LetTuple {key} yts z (insert' e)
    insert' e = LetTmp {key} x t e (changeEnv env' (f e2))
f (LetRec {key} (MkFunDef name args body) e2) = LetRec {key} (MkFunDef name args (f body)) (f e2)
f (LetTuple {key} xts y e) = LetTuple {key} xts y (f e)
f e = e

