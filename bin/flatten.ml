(* type legal = Legal
and ll = LEt
and illegal = Illegal
type (_, _) eq = Eq : ('a, 'a) eq
type _ exp =
  | Unit: legal exp
  | Int : int -> legal exp
  | Float : float -> legal exp
  | Neg : Id.t -> legal exp
  | Add : Id.t * Id.t -> legal exp
  | Sub : Id.t * Id.t -> legal exp
  | FNeg : Id.t -> legal exp
  | FAdd : Id.t * Id.t -> legal exp
  | FSub : Id.t * Id.t -> legal exp
  | FMul : Id.t * Id.t -> legal exp
  | FDiv : Id.t * Id.t -> legal exp
  | IfEq : Id.t * Id.t * 'a exp * 'b exp -> legal exp (* 比較 + 分岐 (caml2html: knormal_branch) *) 
  | IfLE: Id.t * Id.t * legal exp * legal exp -> legal exp (* 比較 + 分岐 *)
  | Let : (Id.t * Type.t) * 'a exp * 'b exp -> ('a, 'b) Letaa.t exp
  | LetRec : (z, _) fundef * (z, _) exp -> (z, _) exp
  | LetTuple : (Id.t * Type.t) list * Id.t * (z, _) exp -> (z, _) exp
  | Var : Id.t -> legal exp
  | App : Id.t * Id.t list -> legal exp
  | Tuple : Id.t list -> legal exp
  | Get : Id.t * Id.t -> legal exp
  | Put : Id.t * Id.t * Id.t -> legal exp
  | ExtArray : Id.t -> legal exp
  | ExtFunApp : Id.t * Id.t list -> legal exp
and ('a, 'b) fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : ('a, 'b) exp }

let name = Id.makeRegister "%fuck"
let u = Type.Unit


let rec f: type a. KNormal.exp -> (z, a) exp = function (** ネストしたletの簡約 (caml2html: assoc_f) *)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, f e1.value, f e2.value)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, f e1.value, f e2.value) 
  | Let(xt, e1, e2) -> (* letの場合 (caml2html: assoc_let) *)
      let rec insert : (z, 'a) exp -> (z, z) exp = fun e -> match e with
        | Let(yt, e3, e4) -> Let(yt, e3, insert e4)
        | LetRec(fundefs, e) -> LetRec(fundefs, insert e)
        | LetTuple(yts, z, e) -> LetTuple(yts, z, insert e)
        | Unit as e -> Let(xt, e, f e2.value)
        | Int _ as e -> Let(xt, e, f e2.value)
        | Float _ as e -> Let(xt, e, f e2.value)
        | Neg _ as e -> Let(xt, e, f e2.value)
        | Add _ as e -> Let(xt, e, f e2.value)
        | Sub _ as e -> Let(xt, e, f e2.value)
        | FNeg _ as e -> Let(xt, e, f e2.value)
        | FAdd _ as e -> Let(xt, e, f e2.value)
        | FSub _ as e -> Let(xt, e, f e2.value)
        | FMul _ as e -> Let(xt, e, f e2.value)
        | FDiv _ as e -> Let(xt, e, f e2.value)
        | IfEq _ as e -> Let(xt, e, f e2.value)
        | IfLE _ as e -> Let(xt, e, f e2.value)
        | Var _ as e -> Let(xt, e, f e2.value)
        | App _ as e -> Let(xt, e, f e2.value)
        | Tuple _ as e -> Let(xt, e, f e2.value)
        | Get _ as e -> Let(xt, e, f e2.value)
        | Put _ as e -> Let(xt, e, f e2.value)
        | ExtArray _ as e -> Let(xt, e, f e2.value)
        | ExtFunApp _ as e -> Let(xt, e, f e2.value)
        in
        let v = f e1.value in
      insert v
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = f e1.value }, f e2.value)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, f e.value)
  | Unit -> Unit | Int(i) -> Int(i) | Float(d) -> Float(d) | Neg(x) -> Neg(x) 
  | Add(x, y) -> Add(x, y) | Sub(x, y) -> Sub(x, y) | FNeg(x) -> FNeg(x) 
  | FAdd(x, y) -> FAdd(x, y) | FSub(x, y) -> FSub(x, y) | FMul(x, y) -> FMul(x, y) 
  | FDiv(x, y) -> FDiv(x, y) | Var(x) -> Var(x) | App(x, ys) -> App(x, ys) | Tuple(xs) -> Tuple(xs) 
  | Get(x, y) -> Get(x, y) | Put(x, y, z) -> Put(x, y, z) | ExtArray(x) -> ExtArray(x) 
  | ExtFunApp(x, ys) -> ExtFunApp(x, ys) *)