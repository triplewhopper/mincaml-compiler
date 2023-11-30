module Alpha 

import Control.Function
import KNormal
import Syntax
import Id


g: KNormal a env -> KNormal a env
g e = e

export
f: KNormal a env -> KNormal a env
f = g