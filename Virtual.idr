module Virtual 

import Binding
import NonNullString
import Data.List
import Data.List1
import Data.Vect
import Data.HVect
import Data.Nat
import Data.String
import Data.DPair
import Data.SortedMap
import Control.Monad.State
import Closure
import Utils

mutual
    data IrTy: Type where
        I1: IrTy
        I8: IrTy
        I32: IrTy
        F32: IrTy
        Label: IrTy
        Ptr: (t: IrTy) -> IrTy
        Struct: {n: Nat} -> (ts: Vect (S n) IrTy) -> IrTy
        Array: (n: Nat) -> (t: IrTy) -> IrTy
        FunPtr: FunTy -> IrTy

    data FunTy: Type where
        MkFunTy: {n: Nat} -> (args: Vect n IrTy) -> (ret: Maybe IrTy) -> FunTy

mutual 
    Show IrTy where
        show I1 = "i1"
        show I8 = "i8"
        show I32 = "i32"
        show F32 = "float"
        show Label = "label"
        show (Ptr t) = show t ++ "*"
        show (Struct ts) = "{ " ++ (joinBy ", " (assert_total show <$> toList ts)) ++ " }"
        show (Array n t) = "[ " ++ show n ++ " x " ++ show t ++ " ]"
        show (FunPtr (MkFunTy args Nothing)) = "void (" ++ (joinBy ", " (assert_total show <$> toList args)) ++ ")"
        show (FunPtr (MkFunTy args (Just ret))) = show ret ++ " (" ++ (joinBy ", " (assert_total show <$> toList args)) ++ ")"


data Const: IrTy -> Type where
    ConstI1: Bool -> Const I1
    ConstInt: Int -> Const I32
    ConstFinN: {n: Nat} -> Fin n -> Const I32
    ConstF32: Double -> Const F32
    ConstArray: {n: Nat} -> (ts: Vect n (Const t)) -> Const (Array n t)
    ConstStruct: (ts: Vect (S n) (DPair IrTy Const)) -> Const (Struct (.fst <$> ts))
    Null: Const (Ptr t)

Show (Const t) where
    show (ConstI1 True) = "true"
    show (ConstI1 False) = "false"
    show (ConstInt i) = show i
    show (ConstFinN x) = show x
    show (ConstF32 f) = show f
    show (ConstArray {n} ts) = "[ " ++ (joinBy ", " (show <$> toList ts)) ++ " ]"
    show (ConstStruct ts) = "{ " ++ (joinBy ", " (toList ((\(_ ** v) => assert_total show v) <$> ts))) ++ " }"
    show Null = "null"


data Kind = Initial | Middle | Terminator

0 MIV: Type 
MIV = Maybe (IdName Variable)

data Reg: IrTy -> Type where
    MkReg: (idx: Nat) -> (t: IrTy) -> MIV -> Reg t

(.ty): Reg t -> IrTy
(.ty) (MkReg _ t _) = t

Show (Reg t) where
    show (MkReg idx _ _) = "%\{show idx}"

data Value: IrTy -> Type where
    ConstV: Const t -> Value t
    RegV: Reg t -> Value t
    GlobalV: {t: IrTy} -> String -> Const t -> Value t

Show (Value t) where
    show (ConstV c) = show c
    show (RegV r) = show r
    show (GlobalV {t} name c) = "@\{name}"

mutual
    data Args: Vect n IrTy -> Type where
        NoArgs: Args []
        (::): Reg t -> (ts: Vect n IrTy) -> Args (t::ts)

    data Ir: {-(Maybe IrTy) -> -} Kind -> Type where
        Alloca: (t: IrTy) ->  (dst: Reg (Ptr t)) -> (align: Nat) -> Ir {- (Just (Ptr t)) -} Middle
        GetElementPtr:  (t: IrTy) -> {r: IrTy} -> (dst: Reg r) -> (src: Reg (Ptr t)) -> (indices: List (Value I32)) -> {auto p: gep t indices = Reg r} -> Ir {- (Just (Ptr r)) -} Middle
        Load:(t: IrTy) -> (dst: Reg t) -> (srcptr: Reg (Ptr t)) -> (align: Nat) -> Ir {- (Just t) -} Middle
        Store: (t: IrTy) -> (src: Value t) -> (destptr: Reg (Ptr t)) -> (align: Nat) -> Ir {- Nothing -} Middle
        BrCond: (cond: Reg I1) -> Reg Label  -> Reg Label -> Ir {- Nothing -} Terminator
        BrLabel: Reg Label -> Ir {- Nothing -} Terminator
        Ret: (t: IrTy) -> (val: Value t) -> Ir {- Nothing -} Terminator
        RetVoid: Ir {- Nothing -} Terminator
        Phi: (t: IrTy) -> (dst: Reg t) -> List1 (Reg t) -> Ir {- (Just t) -} Initial
        Call: (ret: IrTy) -> (dst: Reg ret) -> {n: Nat} -> {argty: Vect n IrTy} -> IrFun (MkFunTy {n} argty (Just ret)) -> (args: Args argty) -> Ir {- (Just ret) -} Middle
        CallVoid: IrFun (MkFunTy {n} argty Nothing) -> (args: Args argty) -> Ir {- Nothing -} Middle
        Add: (t: IrTy) -> (dst: Reg t) -> (v1: Value t) -> (v2: Value t) -> Ir {- (Just t) -} Middle

    data IrFun: FunTy -> Type where
        MkIrFun: (name: IdName Variable) -> (args: Vect n IrTy) -> (ret: Maybe IrTy) -> (blocks: List1 BasicBlock) -> IrFun (MkFunTy args ret)
    
    data BasicBlock: Type where
        MkBB: (idx: Reg Label) -> (nRegAcc:Nat) -> Maybe (Ir Initial) {- (t: IrTy ** Ir (Just t) Initial)-} -> SnocList (Ir Middle) {- (t: Maybe IrTy ** Ir t Middle) -} -> Ir {- Nothing -} Terminator -> BasicBlock
   
    -- data GEP: IrTy -> SnocList (Value I32) -> IrTy -> Type where
    --     ||| getelementptr <ty> <ty>* %x ; yields <ty>*
    --     GEPLin: GEP t [<] (Ptr t) 
    --     ||| getelementptr <struct> <struct>* %x, i32 <idx>
    --     GEPStruct: GEP t (sx :< x') (Ptr (Struct {n} ts)) -> (x: Fin (S n)) -> GEP t (sx :< x' :< ConstV (ConstFinN x)) (Ptr (index x ts))
    --     ||| getelementptr [n x <ty>] <ty>* %x, i32 <idx> ; yields <ty>*
    --     GEPArray: GEP t (sx :< x') (Ptr (Array n t')) -> (x: Value I32) -> GEP t (sx :< x' :< x) (Ptr t')
    --     ||| getelementptr <ty>* 
    --     GEPPtr: (x: Value I32) -> GEP t [< x] (Ptr t)

    0 deref: (t: IrTy) -> (idxes: List (Value I32)) -> Maybe IrTy
    deref t [] = Just t
    deref I1 _ = Nothing
    deref I8 _ = Nothing
    deref I32 _ = Nothing
    deref F32 _ = Nothing
    deref Label _ = Nothing
    deref (Ptr t) (_::_) = Nothing
    deref (Struct {n=n1} ts) (ConstV (ConstFinN {n=n2} x)::xs) = case isLTE n2 (S n1) of
        Yes p => deref (index (weakenLTE x p) ts) xs
        No contra => Nothing
    deref (Struct {n=n1} ts) (ConstV (ConstInt x)::xs) = case integerToFin (cast x) (S n1) of
        Just x => deref (index x ts) xs
        Nothing => Nothing
    deref (Struct ts) (_::_) = Nothing
    deref (Array n t) (x::xs) = deref t xs
    deref (FunPtr _) _ = Nothing

    0 gep: (t: IrTy) -> (indices: List (Value I32)) -> Type
    gep t [] = Reg (Ptr t)
    gep t (_::xs) = case deref t xs of Just r => Reg (Ptr r); Nothing => Void

-- Show (GEP t indices r) where
--     show GEPLin = "0"
--     show (GEPStruct gep x) = show gep ++ ", " ++ show x
--     show (GEPArray gep x) = show gep ++ ", " ++ show x
--     show (GEPPtr x) = show x

Show (Args ts) where
    show NoArgs = ""
    show (x::xs) = show x ++ ", " ++ show xs

Show (Ir k) where 
    show (Alloca t dst Z) = 
        "\{show dst} = alloca \{show t}                      ; yields \{show (Ptr t)}"
    show (Alloca t dst align) = 
        "\{show dst} = alloca \{show t}, align \{show align} ; yields \{show (Ptr t)}"
    show (GetElementPtr t dst src []) = 
        "\{show dst} = getelementptr \{show t}, \{show src.ty} \{show src} ; yields \{show dst.ty}"
    show (GetElementPtr t dst src indices) = 
        "\{show dst} = getelementptr \{show t}, \{show src.ty} \{show src}, \{joinBy ", " ((\i => "i32 \{show i}") <$> indices)} ; yields \{show dst.ty}"
    show (Load t dst srcptr Z) = 
        "\{show dst} = load \{show t}, \{show srcptr.ty} \{show srcptr}"
    show (Load t dst srcptr align) = 
        "\{show dst} = load \{show t}, \{show srcptr.ty} \{show srcptr}, align \{show align}"
    show (Store t src destptr Z) = 
        "store \{show t} \{show src}, \{show destptr.ty} \{show destptr}"
    show (Store t src destptr align) = "store \{show t} \{show src}, \{show destptr.ty} \{show destptr}, align \{show align}"
    show (BrCond cond j1 j2) = "br i1 \{show cond}, label \{show j1}, label \{show j2}"
    show (BrLabel j) = "br label \{show j}"
    show (Ret t val) = "ret \{show t} \{show val}"
    show RetVoid = "ret"
    show (Phi t dst srcs) = "\{show dst} = phi \{show t} \{show srcs}"
    show (Call ret dst (MkIrFun name _ _ _) args) = "\{show dst} = call \{show ret} @\{show name}( \{show args} )"
    show (CallVoid (MkIrFun name _ _ _) args) = "call void @\{show name}(\{show args})"
    show (Add t dst v1 v2) = "\{show dst} = add \{show t} \{show v1}, \{show v2}"


Show BasicBlock where 
    show (MkBB (MkReg idx Label _) nRegAcc Nothing middles terminator) = unlines [show idx ++ ":"] ++ unlines (toList $ indent 4 <$> show <$> middles) ++ unlines [indent 4 $ show terminator]
    show (MkBB (MkReg idx Label _) nRegAcc (Just initial) middles terminator) = unlines [
        show idx ++ ":", indent 4 $ show initial] ++ unlines (toList $ indent 4 <$> show <$> middles) ++ unlines [indent 4 $ show terminator]

nRegAcc: BasicBlock -> Nat
nRegAcc (MkBB _ n _ _ _) = n
label: BasicBlock -> Reg Label
label (MkBB l _ _ _ _) = l

regTy: Ir {- a -} b -> Type 
regTy (Alloca t _ _) = Reg (Ptr t)
regTy (GetElementPtr _ {r} _ _ _) = Reg (Ptr r)
regTy (Load t _ _ _) = Reg t
regTy (Store _ _ _ _) = ()
regTy (BrCond _ _ _) = ()
regTy (BrLabel _) = ()
regTy (Ret t _) = ()
regTy RetVoid = ()
regTy (Phi t _ _) = Reg t
regTy (Call ret _ _ _) = Reg ret
regTy (CallVoid _ _) = ()
regTy (Add t _ _ _) = Reg t

-- regTyLemma: (ir: Ir Nothing b) -> regTy ir = () 
-- regTyLemma (Store _ _ _ _) = Refl
-- regTyLemma (BrCond _ _ _) = Refl
-- regTyLemma (BrLabel _) = Refl
-- regTyLemma RetVoid = Refl
-- regTyLemma (CallVoid _ _) = Refl
-- regTyLemma (Ret _ _) = Refl

-- regTyLemma2: (ir: Ir (Just t) b) -> regTy ir = Reg t
-- regTyLemma2 (Alloca t _ _) = Refl
-- regTyLemma2 (GetElementPtr _ _ _ _) = Refl
-- regTyLemma2 (Load t _ _ _) = Refl
-- regTyLemma2 (Phi t _ _) = Refl
-- regTyLemma2 (Call _ _ _ _) = Refl
-- regTyLemma2 (Add t _ _ _) = Refl

record S where 
    constructor MkS
    nBlocks: Nat
    nRegs: Nat -- number of registers used so far (counting from the beginning of the function arguments)
    blockIdx: Reg Label
    initial: Maybe (Ir Initial) {- (t: IrTy ** Ir (Just t) Initial) -}
    middles: SnocList (Ir Middle) {- (t: Maybe IrTy ** Ir t Middle) -}
    blocks: SnocList BasicBlock
    prf: (nBlocks = length blocks)


complete: S -> Ir {- Nothing -} Terminator -> S
complete (MkS nBlocks nRegs blockIdx initial middles blocks p) terminator = MkS (S nBlocks) nRegs blockIdx Nothing [<] (blocks:<MkBB blockIdx nRegs initial middles terminator) (cong S p)

data IrCommand: (ty: Type) -> S -> (ty -> S) -> Type where
    CLabel: {blockIdx: Reg Label} -> 
        IrCommand (Reg Label) (MkS nBlocks nRegs blockIdx Nothing [<] blks p) (const (MkS nBlocks nRegs blockIdx Nothing [<] blks p))
    CPhi: {nRegs: Nat} -> (t: IrTy) -> (srcs: List1 (Reg t)) -> 
        IrCommand (Reg t) (MkS nBlocks nRegs blockIdx Nothing [<] blks p) (\dst => MkS nBlocks (S nRegs) blockIdx (Just (Phi t dst srcs)) [<] blks p)
    CAlloca: {nRegs: Nat} -> (t: IrTy) -> {default Nothing name: MIV} -> (align: Nat) -> 
        IrCommand (Reg (Ptr t)) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Alloca t dst align)) blks p)
    CGetElementPtr: {nRegs: Nat} -> (t: IrTy) -> {r: IrTy} -> (src: Reg (Ptr t)) -> (indices: List (Value I32)) -> {auto prf: gep t indices = Reg r} -> {default Nothing name: MIV} ->
        IrCommand (Reg r) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(GetElementPtr t dst src indices)) blks p)
    CLoad: {nRegs: Nat} -> (t: IrTy) -> (srcptr: Reg (Ptr t)) -> (align: Nat) -> {default Nothing name: MIV} ->
        IrCommand (Reg t) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Load t dst srcptr align)) blks p)
    CStore: (t: IrTy) -> (src: Value t) -> (destptr: Reg (Ptr t)) -> (align: Nat) -> 
        IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (MkS nBlocks nRegs blockIdx initial (middles:<(Store t src destptr align)) blks p))
    CBrCond: {nRegs: Nat} -> (cond: Reg I1) -> (j1: Reg Label) -> (j2: Reg Label) -> 
        IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (complete (MkS nBlocks nRegs blockIdx initial middles blks p) (BrCond cond j1 j2)))
    CBrLabel: {nRegs: Nat} -> (j: Reg Label) -> 
        IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (complete (MkS nBlocks nRegs blockIdx initial middles blks p) (BrLabel j)))
    CRet: {nRegs: Nat} -> (t: IrTy) -> (val: Value t) ->
        IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (complete (MkS nBlocks nRegs blockIdx initial middles blks p) (Ret t val)))
    CRetVoid: IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (complete (MkS nBlocks nRegs blockIdx initial middles blks p) RetVoid))
    CCall: {nRegs: Nat} -> (ret: IrTy) -> (f: IrFun (MkFunTy {n} argty (Just ret))) -> (args: Args argty) -> {default Nothing name: MIV} ->
        IrCommand (Reg ret) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Call ret dst f args)) blks p)
    CCallVoid: {nRegs: Nat} -> (f: IrFun (MkFunTy {n} argty Nothing)) -> (args: Args argty) -> 
        IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (MkS nBlocks nRegs blockIdx initial (middles:<(CallVoid f args)) blks p))
    CAdd: {nRegs: Nat} -> (t: IrTy) -> (v1: Value t) -> (v2: Value t) -> {default Nothing name: MIV} ->
        IrCommand (Reg t) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Add t dst v1 v2)) blks p)
    -- CAppendInitial: Ir (Just t) Initial -> IrCommand (Ir (Just t) Initial) (MkS nBlocks nRegs Nothing [<] blks p) (\ir => MkS nBlocks nRegs (Just (t ** ir)) [<] blks p)
    -- CAppendMiddle: Ir t Middle -> IrCommand (Ir t Middle) s (appendMiddleS s)
    -- CAppendTerminator: {s: S} -> (terminator: Ir Nothing Terminator) -> IrCommand (Ir Nothing Terminator) s (\ir => complete s ir)
    CBlockEnd: {nBlocks: Nat} -> {blk: BasicBlock} -> {auto 0 p: S nBlocks = S (length blks)} -> 
        IrCommand BasicBlock (MkS (S nBlocks) nRegs blockIdx Nothing [<] (blks:<blk) p) (\blk => MkS (S nBlocks) (nRegAcc blk) (label blk) Nothing [<] (blks:<blk) p)
    -- CNewReg: {nRegs: Nat} -> (t: IrTy) -> IrCommand (Reg t) (MkS nBlocks nRegs initial middles blks p) (\dst => MkS nBlocks (S nRegs) initial middles blks p)
    -- CRegOf: (x: Ir (Just t) b) -> IrCommand (Reg t) s (const s)
    CPure: (x: ty) -> IrCommand ty (st x) st
    (>>=): IrCommand a s1 st1 -> ((x: a) -> IrCommand b (st1 x) st2) -> IrCommand b s1 st2
    (>>): IrCommand () s1 st1 -> IrCommand b (st1 ()) st2 -> IrCommand b s1 st2


getelementptr: {nRegs: Nat} -> (t: IrTy) -> {r: IrTy} -> (src: Reg (Ptr t)) -> (indices: List (Value I32)) -> {auto g: gep t indices = Reg r} ->
IrCommand (Reg r) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(GetElementPtr t dst src indices)) blks p)
-- getelementptr t src idx {g=GEPLin} = CGetElementPtr t src GEPLin
getelementptr t src indices = CGetElementPtr t src indices

alloca: {nRegs: Nat} -> (t: IrTy) -> {default Nothing name: MIV} ->
IrCommand (Reg (Ptr t)) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Alloca t dst 0)) blks p)
alloca t {name} = CAlloca t 0 {name}

store: (t: IrTy) -> (src: Value t) -> (destptr: Reg (Ptr t)) ->
IrCommand () (MkS nBlocks nRegs blockIdx initial middles blks p) (const (MkS nBlocks nRegs blockIdx initial (middles:<(Store t src destptr 0)) blks p))
store t src destptr = CStore t src destptr 0

load: {nRegs: Nat} -> (t: IrTy) -> (srcptr: Reg (Ptr t)) -> {default Nothing name: MIV} ->
IrCommand (Reg t) (MkS nBlocks nRegs blockIdx initial middles blks p) (\dst => MkS nBlocks (S nRegs) blockIdx initial (middles:<(Load t dst srcptr 0)) blks p)
load t srcptr {name} = CLoad t srcptr 0 {name}


%hide Prelude.(>>=)
%hide Prelude.(>>)

test: {nRegs: Nat} -> {blks: SnocList BasicBlock} -> 
IrCommand BasicBlock (MkS (length blks) (S nRegs) (MkReg nRegs Label Nothing) Nothing [<] blks Refl) (\x => MkS (S (length blks)) (nRegAcc x) (label x) Nothing [<] (blks :< x) Refl)
test = do
    l <- CLabel
    -- r1 <- CPhi I32 (MkReg 0 I32:::[MkReg 1 I32])
    r2 <- CAlloca I32 4
    r3 <- CAlloca (Struct [I32, I32]) 4
    r4 <- CLoad I32 r2 4
    arr <- CAlloca (Array 200 I32) 4
    arr3 <- getelementptr (Array 200 I32) arr [ConstV (ConstInt 3), ConstV (ConstInt 0)]
    x <- getelementptr (Struct [I32, I32]) r3 [ConstV (ConstInt 0), ConstV (ConstFinN {n=2} 0)]
    y <- getelementptr (Struct [I32, I32]) r3 [ConstV (ConstInt 0), ConstV (ConstFinN {n=2} 1)]
    CStore I32 (ConstV (ConstInt 1)) x 4
    CStore I32 (ConstV (ConstInt 2)) y 4
    arr3 <- getelementptr I32 arr3 [ConstV (ConstInt 3)]
    CBrLabel l
    CBlockEnd

-- newBlock: {nRegs: Nat} -> {blks: SnocList BasicBlock} -> 
-- Lazy (IrCommand BasicBlock (MkS (length blks) (S nRegs) (MkReg nRegs Label) Nothing [<] blks Refl) (\x => MkS (S (length blks)) (nRegAcc x) (label x) Nothing [<] (blks :< x) Refl)) ->
-- IrCommand BasicBlock (MkS (length blks) (S nRegs) (MkReg nRegs Label) Nothing [<] blks Refl) (\x => MkS (S (length blks)) (nRegAcc x) (label x) Nothing [<] (blks :< x) Refl)
-- newBlock ir = CLabel >>= (\l => ir >>= (\blk => CBlockEnd {blk}))

-- irNot: IrFun (MkFunTy [I1] (Just I1))
-- irNot = MkIrFun "not" [I1] I1 [MkBB 0 Nothing [] (BrCond (MkReg 0 I1) (MkReg 1 (Label 1 Nothing)) (MkReg 2 (Label 2 Nothing))), MkBB 1 Nothing [] (Ret (ConstV (ConstI1 False))), MkBB 2 Nothing [] (Ret (ConstV (ConstI1 True)))]

runCmd: IrCommand ty s st -> ty
runCmd (CPure x) = x
runCmd (CPhi {nRegs} t _) = MkReg nRegs t Nothing
runCmd (CAlloca {nRegs} t {name} _) = MkReg nRegs (Ptr t) name
runCmd (CGetElementPtr {nRegs} {r} t src gep {name}) = MkReg nRegs r name
runCmd (CLoad {nRegs} t _ _ {name}) = MkReg nRegs t name
runCmd (CStore {nRegs} _ _ _ _) = ()
runCmd (CBrCond _ _ _) = ()
runCmd (CBrLabel _) = ()
runCmd (CRet _ _) = ()
runCmd CRetVoid = ()
runCmd (CCall {nRegs} ret _ _ {name}) = MkReg nRegs ret name
runCmd (CCallVoid _ _) = ()
runCmd (CAdd {nRegs} t _ _ {name}) = MkReg nRegs t name
runCmd (CLabel {blockIdx}) = blockIdx
runCmd (CBlockEnd {blk}) = blk
runCmd (ir1 >>= ir2) = runCmd (ir2 (runCmd ir1))
runCmd (ir1 >> ir2) = let () = runCmd ir1 in runCmd ir2

testRes: BasicBlock
testRes = runCmd (test {nRegs=0} {blks=[<]})

fromTy: Ty -> Maybe IrTy
fromTy TyUnit = Nothing
fromTy TyBool = Just I1
fromTy TyI32 = Just I32
fromTy TyF32 = Just F32
fromTy (TyArray t) = Ptr <$> fromTy t
fromTy (TyTuple ts) = case mapMaybe id (fromTy <$> ts) of
    (Z ** [])=> Nothing
    (S n ** ts) => Just (Struct ts)
fromTy (TyFun args ret) = case mapMaybe id (fromTy <$> args) of
    (_ ** args) => Just (FunPtr (MkFunTy args (fromTy ret)))

gen: {arity': Nat} -> FunDef a arity' -> DPair ((p: Nat ** Vect p IrTy), Maybe IrTy) (\((p ** args), ret) => IrFun (MkFunTy {n=p} args ret))
gen (MkFunDef fnbd@(MkFunBinding f argty retty) args formalFv body) = 
    let args' = mapMaybe id (fromTy <$> snd <$> args) in
    let ((p ** args), ret) = (args', fromTy retty) in (((p ** args), ret) ** MkIrFun f args ret irBody)
where
    env0: SortedMap Id (t: IrTy ** Reg t)
    env0': List (Id, (t: IrTy ** Reg t))

    env0 = SortedMap.insertFrom env0' empty

    env0' = snd $ foldl (
        \(i, acc), (name, ty) => 
            case fromTy ty of 
                Just ty => (S i, (MkId name, (ty ** MkReg i ty (Just name)))::acc)
                Nothing => (i, acc)
        ) (0, []) (cast fnbd::toList args ++ formalFv)
    
    genBody: {nRegs: Nat} -> {middles: SnocList (Ir Middle)} -> {env: SortedMap Id (t: IrTy ** Reg t)} -> {units: SortedMap Id Ty} -> Exp a -> 
    IrCommand BasicBlock (MkS 0 nRegs (MkReg 0 Label Nothing) Nothing middles [<] Refl) (\x => MkS 1 (nRegAcc x) (label x) Nothing [<] [<x] Refl)
    irBody: List1 BasicBlock 
    irBody = runCmd (genBody body {env=env0} {nRegs=length (SortedMap.toList env0)} {middles=[<]} {units=empty})  ::: []

    genBody (Let x _ U e2) = genBody {env, units=insert (MkId x) TyUnit units} e2
    genBody (Let x _ (B b) e2) = do 
        xAddr <- alloca I1
        store I1 (ConstV (ConstI1 b)) xAddr
        r <- load I1 xAddr
        genBody {env=insert (MkId x) (I1 ** r) env, units} e2
    genBody (Let x _ (I i) e2) = do
        addr <- alloca I32
        store I32 (ConstV (ConstInt i)) addr
        r <- load I32 addr
        genBody {env=insert (MkId x) (I32 ** r) env, units} e2
    genBody (Let x _ (Fl f) e2) = do
        addr <- alloca F32
        store F32 (ConstV (ConstF32 f)) addr
        r <- load F32 addr
        genBody {env=insert (MkId x) (F32 ** r) env, units} e2
    genBody (Let x t (Var y) e2) = do 
        case fromTy t of 
            Nothing => genBody {env, units=insert (MkId x) t units} e2
            Just t' =>
                case SortedMap.lookup (MkId y) env of 
                    Just tr => genBody {env=insert (MkId x) tr env, units} e2
                    Nothing => warn "in Virtual.genBody: Unbound variable `\{y}`" (genBody {env, units=insert (MkId x) t units} e2)
    genBody (Let x _ (Get y z) e2) = do 
        case SortedMap.lookup y env of 
            Just (Ptr t ** r) => do
                r' <- getelementptr t r [ConstV (ConstInt z)]
                r'' <- load t r'
                genBody {env=insert (MkId x) (t ** r'') env, units} e2
            Just (t ** r) => do
                r' <- getelementptr t r [ConstV (ConstInt z)]
                r'' <- load t r'
                genBody {env=insert (MkId x) (t ** r'') env, units} e2
            Nothing => warn "in Virtual.genBody: Unbound variable `\{y}`" (genBody {env, units} e2)
            
        