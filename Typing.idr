module Typing

import Ty
import Data.Vect
import Data.List
import Decidable.Equality
import Syntax
import Control.App
import Control.App.Console
import Control.App.FileIO
import Data.SortedMap
import Data.String
import System.File.Virtual
import Decidable.Decidable
import Syntax.WithProof

data UnionFindState: Type where 

public export
data MaybeUnified: Type where
    TyUnit: MaybeUnified
    TyI32: MaybeUnified
    TyF32: MaybeUnified
    TyBool: MaybeUnified
    TyTuple: {n: Nat} -> (ts: Vect (2 + n) MaybeUnified) -> MaybeUnified
    TyArray: (t: MaybeUnified) -> MaybeUnified
    TyFun: {n: Nat} -> (ts: Vect (1 + n) MaybeUnified) -> (t: MaybeUnified) -> MaybeUnified
    TyVar: Nat -> MaybeUnified

mutual
    export 
    Show MaybeUnified where
        show TyUnit = "unit"
        show TyI32 = "int"
        show TyF32 = "float"
        show TyBool = "bool"
        show (TyTuple {n=n} ts) = "(\{assert_total show ts})"
        show (TyArray t) = show t ++ " array"
        show (TyFun {n=n} ts t) = "(\{assert_total show ts}) -> \{show t}"
        show (TyVar r) = "'\{show r}"


Cast TypeVar MaybeUnified where
    cast (TyVar r) = TyVar r

Eq MaybeUnified where
    (==) TyUnit TyUnit = True
    (==) TyI32 TyI32 = True
    (==) TyF32 TyF32 = True
    (==) TyBool TyBool = True
    (==) (TyTuple {n=n1} ts1) (TyTuple {n=n2} ts2) with (decEq n1 n2)
        (==) (TyTuple ts1) (TyTuple ts2) | (Yes p) = assert_total (==) ts1  (rewrite p in ts2)
        (==) (TyTuple ts1) (TyTuple ts2) | (No _) = False
    (==) (TyArray t1) (TyArray t2) = t1 == t2
    (==) (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) with (decEq n1 n2)
        (==) (TyFun ts1 t1) (TyFun ts2 t2) | (Yes p) = assert_total (==) ts1  (rewrite p in ts2) && t1 == t2
        (==) (TyFun ts1 t1) (TyFun ts2 t2) | (No _) = False
    (==) (TyVar r1) (TyVar r2) = r1 == r2
    (==) _ _ = False
export
Ord MaybeUnified where
    compare a b = compare (show a) (show b)
public export 
data UnifyErr = UnifyError MaybeUnified MaybeUnified
export 
Show UnifyErr where
    show (UnifyError t1 t2) = "cannot unify `\{show t1}` with `\{show t2}`"

data IsTyVar: MaybeUnified -> Type where
    ItIsTyVar: IsTyVar (TyVar r)

Uninhabited (IsTyVar TyUnit) where
    uninhabited _ impossible
Uninhabited (IsTyVar TyI32) where 
    uninhabited _ impossible
Uninhabited (IsTyVar TyF32) where
    uninhabited _ impossible
Uninhabited (IsTyVar TyBool) where
    uninhabited _ impossible
Uninhabited (IsTyVar (TyTuple ts)) where
    uninhabited _ impossible
Uninhabited (IsTyVar (TyArray t)) where
    uninhabited _ impossible
Uninhabited (IsTyVar (TyFun ts t)) where
    uninhabited _ impossible

isTyVar: (t: MaybeUnified) -> Dec (IsTyVar t)
isTyVar t with (t) proof p
    isTyVar t | (TyVar r) = Yes ItIsTyVar
    isTyVar _ | TyUnit = No absurd 
    isTyVar _ | TyI32 = No absurd
    isTyVar _ | TyF32 = No absurd
    isTyVar _ | TyBool = No absurd
    isTyVar _ | TyTuple ts = No absurd
    isTyVar _ | TyArray t = No absurd
    isTyVar _ | TyFun ts t = No absurd

export 
data TyVarGenState: Type where 

public export
interface TyVarGenI e where 
    gen: () -> App e MaybeUnified

export 
Has [State TyVarGenState Nat] e => TyVarGenI e where 
    gen () = do 
        r <- get TyVarGenState
        put TyVarGenState (r + 1)
        pure (TyVar r)

namespace UnionFind

    data Entry: Type where
        MkEntry: (father: MaybeUnified) -> (rp: Maybe (t: MaybeUnified ** (Not(IsTyVar t)))) -> (rank: Nat) -> Entry
    
    (.father) : Entry -> MaybeUnified
    (.father) (MkEntry father _ _) = father
    (.rp) : (entry: Entry) -> Maybe (t: MaybeUnified ** Not(IsTyVar t))
    (.rp) (MkEntry _ rp _) = rp
    (.rank) : Entry -> Nat
    (.rank) (MkEntry _ _ rank) = rank

    public export
    UnionFind: Type 
    UnionFind = SortedMap MaybeUnified Entry
    public export 
    empty: UnionFind
    empty = the UnionFind SortedMap.empty 

    public export 
    interface UnionFindI e where 
        find: (t: MaybeUnified) -> App e Entry
        merge: (t1: MaybeUnified) -> (t2: MaybeUnified) -> {auto 0 p: IsTyVar t1} -> App e ()

    export
    Has [Exception UnifyErr, State UnionFindState UnionFind] e => UnionFindI e where
        find t = do 
            case SortedMap.lookup t !(get UnionFindState) of
                Nothing =>
                    case isTyVar t of
                        Yes p' => do
                            let entry = MkEntry t Nothing 0 
                            modify UnionFindState (insert t entry)
                            pure entry
                        No contra => do 
                            let entry = MkEntry t (Just (t ** contra)) 0
                            modify UnionFindState (insert t entry)
                            pure entry
                Just entry => do 
                    if entry.father == t then pure entry else do
                        entry' <- find entry.father
                        modify UnionFindState (insert t entry')
                        pure entry'

        merge t1 t2 = do 
            entry1 <- find t1
            entry2 <- find t2
            if entry1.father == entry2.father then pure () else do
                let dec1 = isTyVar entry1.father
                let dec2 = isTyVar entry2.father
                (entry1, entry2) <- case (dec1, dec2) of
                    (Yes p1, Yes p2) => pure (entry1, entry2)
                    (Yes p1, No contra2) => do 
                        let entry1' = {rp:= Just (entry2.father ** contra2)} entry1
                        modify UnionFindState (insert entry1.father entry1')
                        pure (entry1', entry2)
                    (No contra1, Yes p2) => do
                        let entry2' = {rp:= Just (entry1.father ** contra1)} entry2
                        modify UnionFindState (insert entry2.father entry2')
                        pure (entry1, entry2')
                    (No contra1, No contra2) => throw (UnifyError entry1.father entry2.father)
                case compare entry1.rank entry2.rank of
                    LT => do 
                        let entry1' = MkEntry entry2.father entry1.rp entry1.rank
                        modify UnionFindState (insert entry1.father entry1')
                    EQ => do 
                        let entry2' = MkEntry entry1.father entry2.rp (entry2.rank + 1)
                        modify UnionFindState (insert entry2.father entry2')
                    GT => do 
                        let entry2' = MkEntry entry1.father entry1.rp entry2.rank
                        modify UnionFindState (insert entry2.father entry2')

data FullyUnified: MaybeUnified -> Type where
    FullyUnifiedUnit: FullyUnified TyUnit
    FullyUnifiedI32: FullyUnified TyI32
    FullyUnifiedF32: FullyUnified TyF32
    FullyUnifiedBool: FullyUnified TyBool
    FullyUnifiedTuple2: (FullyUnified t1) -> (FullyUnified t2) -> FullyUnified (TyTuple [t1, t2])
    FullyUnifiedTuple: (FullyUnified t) -> (FullyUnified (TyTuple ts)) -> FullyUnified (TyTuple (t :: ts))
    FullyUnifiedArray: (FullyUnified t) -> FullyUnified (TyArray t)
    FullyUnifiedFun1: (FullyUnified t1) -> (FullyUnified t2) -> FullyUnified (TyFun [t1] t2)
    FullyUnifiedFun: (FullyUnified t1) -> (FullyUnified (TyFun ts t1)) -> FullyUnified (TyFun (t :: ts) t1)

export 
unify: (t1: MaybeUnified) -> (t2: MaybeUnified) -> Has [Exception UnifyErr, UnionFindI] e => App e ()
unify TyUnit TyUnit = pure ()
unify TyI32 TyI32 = pure ()
unify TyF32 TyF32 = pure ()
unify TyBool TyBool = pure ()
unify (TyTuple {n=n1} ts1) (TyTuple {n=n2} ts2) with (decEq n1 n2)
    unify (TyTuple {n=n1} ts1) (TyTuple {n=n2} ts2) | (Yes p) = let (>>=) = App.(>>=) in foldl (\acc, (t1, t2) =>  acc >>= (\() => unify t1 t2)) (pure ()) (zip ts1 (rewrite p in ts2)) 
    unify (TyTuple {n=n1} ts1) (TyTuple {n=n2} ts2) | (No _) = throw (UnifyError (TyTuple ts1) (TyTuple ts2))
unify (TyArray t1) (TyArray t2) = unify t1 t2
unify (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) with (decEq n1 n2)
    unify (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (Yes p) = let (>>=) = App.(>>=) in foldl (\acc, (t1, t2) => acc >>= (\() => unify t1 t2)) (unify t1 t2) (zip ts1 (rewrite p in ts2))
    unify (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (No p) = throw (UnifyError (TyFun ts1 t1) (TyFun ts2 t2))
unify (TyVar r1) t = merge (TyVar r1) t
unify t (TyVar r2) = merge (TyVar r2) t
unify t1 t2 = throw (UnifyError t1 t2)

export
data ExtEnvState: Type where 
    
public export
interface ExtEnvI e where 
    findExt: (x: String) -> App e (Maybe MaybeUnified)
    extend: (x: String) -> (t: MaybeUnified) -> App e ()
    get: () -> App e (List (String, MaybeUnified))
    
export 
Has[State ExtEnvState (List (String, MaybeUnified))] e => ExtEnvI e where 
    findExt x = do 
        env <- get ExtEnvState
        pure (lookup x env)
    extend x t = do 
        env <- get ExtEnvState
        put ExtEnvState ((x, t)::env)
    get () = do 
        env <- get ExtEnvState
        pure env

public export
interface EConsole e where 
    eprintLn: (s: String) -> App e ()

export 
Has [FileIO, Console] e => EConsole e where
    eprintLn s = fPutStrLn stderr s

export
infer:  {env: List (String, TypeVar)} -> (expr: Node) -> Has [Exception UnifyErr, EConsole, UnionFindI, TyVarGenI, ExtEnvI] e => App e MaybeUnified
infer (U) = pure TyUnit
infer (I _) = pure TyI32
infer (B _) = pure TyBool
infer (F _) = pure TyF32
infer {env} (Not n) = do ty <- infer {env} n; unify ty TyBool; pure TyBool
infer {env} (Neg n) = do ty <- infer {env} n; unify ty TyI32; pure TyI32
infer {env} (Add n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyI32; unify ty2 TyI32; pure TyI32
infer {env} (Sub n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyI32; unify ty2 TyI32; pure TyI32
infer {env} (FNeg n) = do ty <- infer {env} n; unify ty TyF32; pure TyF32
infer {env} (FAdd n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyF32; unify ty2 TyF32; pure TyF32
infer {env} (FSub n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyF32; unify ty2 TyF32; pure TyF32
infer {env} (FMul n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyF32; unify ty2 TyF32; pure TyF32
infer {env} (FDiv n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 TyF32; unify ty2 TyF32; pure TyF32
infer {env} (Eq n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (Neq n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (Lt n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (Le n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (Gt n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (Ge n1 n2) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; unify ty1 ty2; pure TyBool
infer {env} (If n1 n2 n3) = do ty1 <- infer {env} n1; ty2 <- infer {env} n2; ty3 <- infer {env} n3; unify ty1 TyBool; unify ty2 ty3; pure ty2
infer {env} (Let x ty n1 n2) = do ty1 <- infer {env} n1; unify (cast ty) ty1; infer {env=(x,ty)::env} n2
infer {env} (LetTuple xs tys n1 n2) = do 
    ty1 <- infer {env} n1
    unify ty1 (cast (TyTuple $ map cast tys))
    infer {env=(reverse $ toList $ zip xs tys) ++ env} n2
infer {env} (LetRec {nArgs} (MkFunDef name ty args argsTy body) n2) = do 
    let env = (name, ty)::env
    let ty' = cast ty
    let argsTy' = map cast argsTy
    let env' = (reverse $ toList $ zip args argsTy) ++ env
    res <- infer {env = env'} 
    let func = TyFun argsTy' res
    unify ty' func
    infer {env} n2
infer {env} (Var x) = do 
    case lookup x env of
        Just ty => pure (cast ty)
        Nothing => case !(findExt x) of
            Just ty => pure (cast ty)
            Nothing => do 
                ty <- gen ()
                -- ty <- pure (TyVar 0)
                extend x ty
                eprintLn $ "[warning] free variable `\{x}` assumed as external."
                pure ty
infer {env} (Put (Get n1 n2) n3) = do
    ty3 <- infer {env} n3; unify ty3 TyI32
    ty1 <- infer {env} n1; unify ty1 (TyArray ty3)
    ty2 <- infer {env} n2; unify ty2 TyI32
    pure TyUnit
infer {env} (Get n1 n2) = do 
    ty1 <- infer {env} n1
    a <- gen ()
    -- a <- pure (TyVar 0)
    unify ty1 (TyArray a)
    ty2 <- infer {env} n2
    unify ty2 TyI32
    pure a
    