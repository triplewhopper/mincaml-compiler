type error_kind = Known of {ast:Syntax.ast;got:Type.t;expected:Type.t}| Unknown of Syntax.ast [@@deriving show]
exception Error of error_kind
val extenv : Type.t M.t ref
val f : Syntax.ast -> Syntax.ast

