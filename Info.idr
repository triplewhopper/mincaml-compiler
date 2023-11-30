module Info

import Text.Lexer
import Control.Function
import Decidable.Equality

public export
data NodeKeyType: Type where
    NodeKey: Nat -> NodeKeyType

export
Show NodeKeyType where
    show (NodeKey x) = show x

public export
Eq NodeKeyType where
    (==) (NodeKey x) (NodeKey y) = x == y

public export 
Injective NodeKey where
    injective Refl = Refl

public export
DecEq NodeKeyType where
    decEq (NodeKey x) (NodeKey y) = decEqCong (decEq x y)

public export
Ord NodeKeyType where
    compare (NodeKey x) (NodeKey y) = compare x y

public export
interface Info a where
    (.key): a -> NodeKeyType
    (.span): a -> Bounds
    (.new): a -> a

export
(Info a) => Eq a where 
    (==) x y = x.key == y.key
export 
(Info a) => Ord a where 
    compare x y = compare x.key y.key
