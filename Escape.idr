module Escape 

import Id 
import Ty
import KNormal
import NonNullString
import Data.Vect
import Data.Vect.Elem
import Data.Fin

data Field: IdName Variable -> Ty -> Type where
    MkField: (x: IdName Variable) -> (i: Fin (2 + n)) -> Field x (TyTuple {n} ts)

data FieldAlias: Id -> IdName Variable -> Ty -> Type where
    MkFieldAlias: (x: Id) -> (x': IdName Variable) -> (i: Fin (2 + n)) -> FieldAlias x x' (TyTuple {n} ts)

data Alias: Id -> IdName Variable -> KNormal a env -> Type where
    AliasLet: (x: IdName Variable) -> (t: Ty) -> (x': IdName Variable) -> (e: KNormal a ((x, t)::env)) -> Alias (MkId x) x' (Let {key} x t (Var x') e)
    AliasLet': (x: IdName Variable) -> (t: Ty) -> Alias (MkId x) x' e -> (e': KNormal a ((x, t)::env)) -> Alias (MkId x) x' (Let {key} x t e e')
    AliasLetTmp: (x: IdName Temporary) -> (t: Ty) -> (x': IdName Variable) -> (e: KNormal a env) -> Alias (MkId x) x' (LetTmp {key} x t (Var x') e)
    AliasLetTmp': (x: IdName Temporary) -> (t: Ty) -> Alias (MkId x) x' e -> (e': KNormal a env) -> Alias (MkId x) x' (LetTmp {key} x t e e')
    -- AliasLetTuple: 