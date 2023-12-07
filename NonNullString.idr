module NonNullString

import Data.So
import Decidable.Equality
import Text.Lexer
import Text.PrettyPrint.Prettyprinter

public export 
data NonNullString: Type where 
    MkNonNullStr: (s: String) -> {auto p: So (s /= "")} -> NonNullString

export
Show NonNullString where 
    show (MkNonNullStr s) = show s 
export 
Interpolation NonNullString where 
    interpolate (MkNonNullStr s) = s
export
Eq NonNullString where 
    (MkNonNullStr s1) == (MkNonNullStr s2) = s1 == s2

export 
DecEq NonNullString where 
    decEq (MkNonNullStr s1) (MkNonNullStr s2) = case decEq s1 s2 of 
        Yes _ => Yes (believe_me 1)
        No contra => No believe_me

export
Ord NonNullString where 
    compare (MkNonNullStr s1) (MkNonNullStr s2) = compare s1 s2

export 
Pretty NonNullString where 
    pretty (MkNonNullStr s) = pretty s

export 
Cast NonNullString String where 
    cast (MkNonNullStr s) = s

export 
(++): NonNullString -> NonNullString -> NonNullString
MkNonNullStr s1 ++ MkNonNullStr s2 = MkNonNullStr (s1 ++ s2) {p=believe_me 1}

infixr 7 +++
export
(+++): String -> NonNullString -> NonNullString
s1 +++ MkNonNullStr s2 = MkNonNullStr (s1 ++ s2) {p=believe_me 1}
