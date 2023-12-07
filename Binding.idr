module Binding 

import public Id 
import public Ty 
import public Data.Vect
import public Decidable.Equality

public export
0 Binding: Type 
Binding = (IdName Variable, Ty)

public export
record FunBinding (n': Nat) where 
    constructor MkFunBinding 
    name: IdName Variable
    argty: Vect (S n') Ty
    retty: Ty

public export
(.fnty): {n': Nat} -> FunBinding n' -> Ty
(.fnty) {n'=S _} (MkFunBinding _ argty retty) = TyFun (TyTuple argty) retty
(.fnty) {n'=0} (MkFunBinding _ [argty] retty) = TyFun argty retty

export 
{n': Nat} -> Cast (FunBinding n') Binding where 
    cast fnbd = (fnbd.name, fnbd.fnty)

export
Eq (FunBinding n') where 
    (==) (MkFunBinding name1 argty1 retty1) (MkFunBinding name2 argty2 retty2) = 
        name1 == name2 && argty1 == argty2 && retty1 == retty2

-- export 
-- DecEq (FunBinding n') where 
--     decEq (MkFunBinding n1 a1 r1) (MkFunBinding n2 a2 r2) with (decEq n1 n2) | (decEq a1 a2) 
--         decEq (MkFunBinding n1 a1 r1) (MkFunBinding n2 a2 r2) | Yes n1'eq'n2 | Yes a1'eq'a2 with (decEq r1 r2)
--             decEq (MkFunBinding n1 a1 r1) (MkFunBinding n2 a2 r2) | Yes n1'eq'n2 | Yes a1'eq'a2 | Yes r1'eq'r2 = 
--             decEq (MkFunBinding n1 a1 r1) (MkFunBinding n2 a2 r2) | Yes n1'eq'n2 | Yes a1'eq'a2 | No r1'neq'r2 = No $ \r1'eq'r2 => r1'neq'r2 (rewrite n1'eq'n2 in rewrite a1'eq'a2 in r1'eq'r2)