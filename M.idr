module M

import Data.Vect
import Data.List
import Data.List.Elem
import Ty
import Cyntax as Syntax

public export
data M: Type -> Type -> Type where
  MkM: (a -> (b, a)) -> M a b

export
Functor (M a) where
  map f (MkM g) = MkM (\n => let (x, n') = g n in (f x, n'))

export
Applicative (M a) where
  pure x = MkM (\n => (x, n))
  (MkM f) <*> (MkM g) = MkM (\n => let (x, n') = f n in let (y, n'') = g n' in (x y, n''))

export
Monad (M a) where
  (MkM f) >>= g = MkM (\n => let (x, n') = f n in let MkM h = g x in h n')

public export
bind: Monad m => m a -> (a -> m b) -> m b
bind = Prelude.(>>=)

export
runState: s -> M s a -> a
runState s0 (MkM f) = fst (f s0)

