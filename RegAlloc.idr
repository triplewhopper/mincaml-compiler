module RegAlloc 

import Data.Fin 
import Data.SortedMap
import Data.SortedSet
import Id


RegMap: Type 
RegMap = SortedMap (IdName Register) (c: CallingConvention ** ABIReg c)

save: IdName Register -> ABIReg Caller -> RegMap -> RegMap
restore: IdName Register -> ABIReg Caller -> RegMap -> RegMap

data Edge: Type -> Type -> Type where 
    MkEdge: (to: v) -> a -> Edge a v

data Graph: (a: Type) -> (v: Type) -> Edge a v -> Type where 
    Empty: Graph a v e
    (:+:): (v, List (Edge a v)) -> Graph a v e -> Graph a v e

data Queue: Type -> Type where 
    MkQ: (front: List a) -> (back: List a) -> (deposit: Nat) -> Queue a

emptyQ: Queue a
emptyQ = MkQ [] [] 0

-- push: a -> Queue a -> Queue a
-- push x (MkQ front back deposit) = MkQ front (x :: back) (deposit + 1)

-- pop: Queue a -> Maybe (a, Queue a)
-- pop (MkQ [] [] _) = Nothing
-- pop (MkQ front [] deposit) = pop (MkQ [] (reverse front) 0)
-- pop (MkQ front (x :: back) (S deposit)) = Just (x, MkQ front back deposit)


-- infixl 7 :+:

-- deg: (Eq v) => Graph a v e -> v -> Nat
-- deg Empty _ = 0
-- deg ((v, edges) :+: rest) v' = if v == v' then length edges else deg rest v'

-- bfsOn: (Monad m, Alternative m, Ord v) => Graph a v e -> SortedSet v -> (v -> List (Edge a v) -> m b) -> m b
-- bfsOn Empty _ _ = empty
-- bfsOn ((v, edges) :+: rest) visited f = 
--     if v `elem` visited then bfs rest visited f
--     else f v edges <|> bfs rest (insert v visited) f