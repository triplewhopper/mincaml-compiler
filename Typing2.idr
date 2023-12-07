module Typing2
import Ty
import NonNullString
import Info
import Data.Vect
import Data.List
import Data.Vect.Elem
import Data.List1
import Data.Either
import Decidable.Equality
import Syntax
import Data.SortedMap
import Data.String
import Text.Lexer
import System.File.Virtual
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.State.State
import Control.Monad.State.Interface
import Control.Monad.Either
import Control.Monad.Identity
import Control.Monad.Error.Interface
import Control.Monad.RWS
import Utils

0 isPreludeCon: String -> Type 
isPreludeCon s = Elem s ["unit", "int", "float", "bool", "array", "tuple", "->"]


data Ty0: Type where
    TyCon: {n: Nat} -> (name: String) -> {auto p: isPreludeCon name} -> (ts: Vect n Ty0) -> Ty0
    -- TyUnit: Ty0
    -- tI32: Ty0
    -- tF32: Ty0
    -- tBool: Ty0
    -- TyTuple: {n: Nat} -> (ts: Vect (2 + n) Ty0) -> Ty0
    -- TyArray: Ty0 -> Ty0
    -- -- TyFun: {n: Nat} -> (ts: Vect (1 + n) Ty0) -> Ty0 -> Ty0
    -- TyFun : Ty0 -> Ty0 -> Ty0
    TyVar: Nat -> Ty0

tUnit, tI32, tF32, tBool: Ty0
tUnit = TyCon "unit" []
tI32 = TyCon "int" []
tF32 = TyCon "float" []
tBool = TyCon "bool" []

tArray: Ty0 -> Ty0
tArray t = TyCon "array" [t] 

tTuple: {n: Nat} -> (ts: Vect (2 + n) Ty0) -> Ty0
tTuple ts = TyCon "tuple" ts

infixr 4 `fn`
fn: Ty0 -> Ty0 -> Ty0
fn t1 t2 = TyCon "->" [t1, t2]

Show Ty0 where
    show (TyCon {n=n} name ts) = "\{name} \{if n == 0 then "" else "(" ++ (", " `joinBy` assert_total show <$> toList ts) ++ ")"}"
    -- show TyUnit = "unit"
    -- show tI32 = "int"
    -- show tF32 = "float"
    -- show tBool = "bool"
    -- show (TyTuple {n=n} ts) = "(\{", " `joinBy` assert_total show <$> toList ts})"
    -- show (TyArray t) = show t ++ " array"
    -- show (TyFun {n=n} ts t) = "(\{", " `joinBy` assert_total show <$> toList ts}) -> \{show t}"
    -- show (TyFun t1 t2) = "\{show t1} -> \{show t2}"
    show (TyVar r) = "'\{show r}"


-- Cast TypeVar Ty0 where
--     cast (TyVar r) = TyVar r

Eq Ty0 where
    -- (==) TyUnit TyUnit = True
    -- (==) tI32 tI32 = True
    -- (==) tF32 tF32 = True
    -- (==) tBool tBool = True
    -- (==) (TyTuple {n=n1} ts1) (TyTuple {n=n2} ts2) with (decEq n1 n2)
        -- (==) (TyTuple ts1) (TyTuple ts2) | (Yes p) = assert_total (==) ts1  (rewrite p in ts2)
        -- (==) (TyTuple ts1) (TyTuple ts2) | (No _) = False
    -- (==) (TyArray t1) (TyArray t2) = t1 == t2
    -- (==) (TyFun a b) (TyFun c d) = a == c && b == d
    -- (==) (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) with (decEq n1 n2)
    --     (==) (TyFun ts1 t1) (TyFun ts2 t2) | (Yes p) = assert_total (==) ts1  (rewrite p in ts2) && t1 == t2
    --     (==) (TyFun ts1 t1) (TyFun ts2 t2) | (No _) = False
    (==) (TyCon {n=n1} name1 ts1) (TyCon {n=n2} name2 ts2) with (decEq n1 n2)
        (==) (TyCon name1 ts1) (TyCon name2 ts2) | (Yes p) = name1 == name2 && assert_total (==) ts1 (rewrite p in ts2)
        (==) (TyCon name1 ts1) (TyCon name2 ts2) | (No _) = False
    (==) (TyVar r1) (TyVar r2) = r1 == r2
    (==) _ _ = False

Ord Ty0 where
    compare a b = compare (show a) (show b)

public export 
data UnifyError = UnifyErr String Ty0 Ty0

export 
Show UnifyError where
    show (UnifyErr msg t1 t2) = msg ++ "cannot unify `\{show t1}` with `\{show t2}`"

data IsTyVar: Ty0 -> Type where
    ItIsTyVar: IsTyVar (TyVar r)

{name: String} -> {p: isPreludeCon name} -> {ts: Vect n Ty0} -> Uninhabited (IsTyVar (TyCon name ts)) where
    uninhabited (TyCon {n} name ts) impossible

-- Uninhabited (IsTyVar TyUnit) where
--     uninhabited _ impossible
-- Uninhabited (IsTyVar tI32) where 
--     uninhabited _ impossible
-- Uninhabited (IsTyVar tF32) where
--     uninhabited _ impossible
-- Uninhabited (IsTyVar tBool) where
--     uninhabited _ impossible
-- Uninhabited (IsTyVar (TyTuple ts)) where
--     uninhabited _ impossible
-- Uninhabited (IsTyVar (TyArray t)) where
--     uninhabited _ impossible
-- Uninhabited (IsTyVar (TyFun ts t)) where
--     uninhabited _ impossible

isTyVar: (t: Ty0) -> Dec (IsTyVar t)
isTyVar t with (t) proof p
    isTyVar t | (TyVar _) = Yes ItIsTyVar
    isTyVar t | (TyCon _ _) = No absurd
    -- isTyVar _ | TyUnit = No absurd 
    -- isTyVar _ | tI32 = No absurd
    -- isTyVar _ | tF32 = No absurd
    -- isTyVar _ | tBool = No absurd
    -- isTyVar _ | TyTuple ts = No absurd
    -- isTyVar _ | TyArray t = No absurd
    -- isTyVar _ | TyFun ts t = No absurd

namespace UnionFind
    data Entry: Type where
        MkEntry: (father: Ty0) -> (rp: Maybe (t: Ty0 ** (Not(IsTyVar t)))) -> (rank: Nat) -> Entry
    
    export
    (.father) : Entry -> Ty0
    (.father) (MkEntry father _ _) = father

    export
    (.rp) : (entry: Entry) -> Maybe (t: Ty0 ** Not(IsTyVar t))
    (.rp) (MkEntry _ rp _) = rp

    (.rank) : Entry -> Nat
    (.rank) (MkEntry _ _ rank) = rank

    public export
    UnionFind: Type 
    UnionFind = SortedMap Ty0 Entry
    public export 
    empty: UnionFind
    empty = the UnionFind SortedMap.empty 

    public export
    data MergeError: Type where
        MergeErr: Ty0 -> Ty0 -> MergeError

    public export
    interface (Monad m) => UnionFindI m where
        find: (t: Ty0) -> StateT UnionFind m Entry
        merge: (t1: Ty0) -> (t2: Ty0) -> {auto 0 p: IsTyVar t1} -> EitherT MergeError (StateT UnionFind m) ()
    -- public export
    -- (Monad m, UnionFindI m) => UnionFindI (StateT s m) where
    --   find t = lift (find t)
    --   merge t1 t2 = lift (merge t1 t2)
    export
    (Monad m) => UnionFindI m where
        find t = do 
            case !(gets (SortedMap.lookup t)) of
                Nothing =>
                    case isTyVar t of
                        Yes p' => do
                            let entry = MkEntry t Nothing 0 
                            modify (insert t entry)
                            pure entry
                        No contra => do 
                            let entry = MkEntry t (Just (t ** contra)) 0
                            modify (insert t entry)
                            pure entry
                Just entry => do 
                    if entry.father == t then pure entry else do
                        entry' <- find entry.father
                        modify (insert t entry')
                        pure entry'
        merge t1 t2 = do 
            -- info ("merge: " ++ show t1 ++ " " ++ show t2) pure ()
            entry1 <- lift $ find t1
            entry2 <- lift $ find t2
            -- info ("rp: " ++ show (fst <$> entry1.rp) ++ " " ++ show (fst <$> entry2.rp)) pure ()
            -- info ("fa: " ++ show entry1.father ++ " " ++ show entry2.father) pure ()
            if entry1.father == entry2.father then pure () else do
                (entry1, entry2) <- case (entry1.rp, entry2.rp) of
                    (Nothing, Nothing) => pure (entry1, entry2)
                    (Nothing, Just rp2) => do 
                        let entry1' = {rp:= Just rp2} entry1
                        modify (insert entry1.father entry1')
                        pure (entry1', entry2)
                    (Just rp1, Nothing) => do
                        let entry2' = {rp:= Just rp1} entry2
                        modify (insert entry2.father entry2')
                        pure (entry1, entry2')
                    (Just (rp1 ** _), Just (rp2 ** _)) => throwError (MergeErr rp1 rp2)
                case compare entry1.rank entry2.rank of
                    LT => do 
                        let entry1' = MkEntry entry2.father entry1.rp entry1.rank
                        modify (insert entry1.father entry1')
                    EQ => do 
                        let entry2' = MkEntry entry1.father entry2.rp (S entry2.rank)
                        modify (insert entry2.father entry2')
                    GT => do 
                        let entry2' = MkEntry entry1.father entry2.rp entry2.rank
                        modify (insert entry2.father entry2')
    export 
    Show UnionFind where 
        show uf = show uf' 
        where uf': List (List1 (Ty0, Ty0))
              uf' = ((\(k, v) => (k, v.father)) <$>) <$> groupAllWith (\(k, v) => (.father) . snd $ runIdentity(runStateT uf (assert_total find k))) (SortedMap.toList uf)

data FullyUnified: Ty0 -> Type where
    FullyUnifiedCon: {n: Nat} -> (name: String) -> {auto _: isPreludeCon name} -> (ts: Vect n (t: Ty0 ** FullyUnified t)) -> FullyUnified (TyCon name (.fst <$> ts))
    -- FullyUnifiedUnit: FullyUnified TyUnit
    -- FullyUnifiedI32: FullyUnified tI32
    -- FullyUnifiedF32: FullyUnified tF32
    -- FullyUnifiedBool: FullyUnified tBool
    -- FullyUnifiedTuple: (ts: Vect (2 + n) (t: Ty0 ** FullyUnified t)) -> FullyUnified (TyTuple (fst <$> ts))
    -- FullyUnifiedArray: (FullyUnified t) -> FullyUnified (TyArray t)
    -- FullyUnifiedFun: (ts: Vect (1 + n) (t: Ty0 ** FullyUnified t)) -> (t: Ty0 ** FullyUnified t) -> FullyUnified (TyFun (fst <$> ts) (fst t))

interface UnifyI m where
    unify: Ty0 -> Ty0 -> EitherT UnifyError (StateT UnionFind m) ()

(Monad m) => UnifyI m where
    unify t1 t2 = do
        entry1 <- lift $ find t1
        entry2 <- lift $ find t2
        unify' (fromMaybe entry1.father (fst <$> entry1.rp)) (fromMaybe entry2.father (fst <$> entry2.rp))
    where
        unify': (t1: Ty0) -> (t2: Ty0) -> EitherT UnifyError (StateT UnionFind m) ()
        -- unify' TyUnit TyUnit = pure ()
        -- unify' tI32 tI32 = pure ()
        -- unify' tF32 tF32 = pure ()
        -- unify' tBool tBool = pure ()
        -- unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) with (decEq n1 n2)
            -- unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) | (Yes p) = (foldlM (\() => uncurry unify) () (zip ts1 (rewrite p in ts2))) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show tu1}` and `\{show tu2}`: " t1 t2))
            -- unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) | (No _) = throwError (UnifyErr "different length tuple type" (TyTuple ts1) (TyTuple ts2))
        -- unify' (TyArray t1) (TyArray t2) = unify t1 t2
        -- unify' (TyFun t1 t2) (TyFun t3 t4) = (unify t1 t3 >> unify t2 t4) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show (TyFun t1 t2)}` and `\{show (TyFun t3 t4)}`: " t1 t2))
        -- unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) with (decEq n1 n2)
        --     unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (Yes p) = foldlM (\() => uncurry unify) !(unify t1 t2) (zip ts1 (rewrite p in ts2)) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show (TyFun ts1 t1)}` and `\{show (TyFun ts2 t2)}`: " t1 t2))
        --     unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (No p) = throwError (UnifyErr "" (TyFun ts1 t1) (TyFun ts2 t2))
        unify' (TyCon {n=n1} name1 ts1) (TyCon {n=n2} name2 ts2) with (decEq name1 name2) | (decEq n1 n2)
            unify' (TyCon {n=n1} name1 ts1) (TyCon {n=n2} name2 ts2) | Yes _ | Yes p = (foldlM (\() => uncurry unify) () (zip ts1 (rewrite p in ts2))) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show (TyCon name1 ts1)}` and `\{show (TyCon name2 ts2)}`: " t1 t2))
            unify' (TyCon {n=n1} name1 ts1) (TyCon {n=n2} name2 ts2) | Yes _ | No _ = throwError (UnifyErr "different arity" (TyCon name1 ts1) (TyCon name2 ts2))
            unify' (TyCon {n=n1} name1 ts1) (TyCon {n=n2} name2 ts2) | No _ | _ = throwError (UnifyErr "different name" (TyCon name1 ts1) (TyCon name2 ts2))
        unify' (TyVar r1) t = merge (TyVar r1) t `catchE` (\(MergeErr t1 t2) => throwError (UnifyErr "when unifying \{show (TyVar r1)} and \{show t}: " t1 t2))
        unify' t (TyVar r2) = merge (TyVar r2) t `catchE` (\(MergeErr t1 t2) => throwError (UnifyErr "when unifying \{show (TyVar r2)} and \{show t}: " t1 t2))
        unify' t1 t2 = throwError (UnifyErr "" t1 t2)

occursIn: (x: Ty0) -> {auto p: IsTyVar x} -> (t: Ty0) -> EitherT Bool (State UnionFind) Bool 
-- occursIn x TyUnit = pure False
-- occursIn x tI32 = pure False
-- occursIn x tF32 = pure False
-- occursIn x tBool = pure False
-- occursIn x (TyTuple ts) = do 
--     bs <- traverse (occursIn x) ts
--     pure (foldl (\acc, b => acc || b) False bs)
-- occursIn x (TyArray t) =  x `occursIn` t
-- occursIn x (TyFun arg t) = do 
--     -- bs <- traverse (occursIn x) ts
--     when !(x `occursIn` arg) (throwError True)
--     when !(x `occursIn` t) (throwError True)
--     pure False
occursIn x (TyCon {n=n} name ts) = do 
    bs <- traverse (occursIn x) ts
    pure (foldl (\acc, b => acc || b) False bs)
occursIn x t@(TyVar x2) = do 
    if x == t then throwError True else do
        entry <- lift $ find t
        case entry.rp of
            Nothing => pure False
            Just (t ** contra) => x `occursIn` t

data RecursiveOccurenceError: Type where
    RecursiveOccurenceErr: (x: Ty0) -> {auto p: IsTyVar x} -> Ty0 -> RecursiveOccurenceError

export 
Show RecursiveOccurenceError where
    show (RecursiveOccurenceErr x t) = "recursive occurence of `\{show x}` in `\{show t}`"

apply: (t: Ty0) -> StateT UnionFind (Either RecursiveOccurenceError) Ty0
apply x with (isTyVar x) proof p
    -- apply TyUnit | No _ = pure (TyUnit ** FullyUnifiedUnit)
    -- apply tI32 | No _ = pure (tI32 ** FullyUnifiedI32)
    -- apply tF32 | No _ = pure (tF32 ** FullyUnifiedF32)
    -- apply tBool | No _ = pure (tBool ** FullyUnifiedBool)
    -- apply (TyTuple ts) | No _ = do 
    --     ts' <- traverse apply ts
    --     pure (TyTuple (fst <$> ts') ** (FullyUnifiedTuple ts'))
    -- apply (TyArray t) | No _ = do
    --     (t' ** p) <- apply t
    --     pure (TyArray t' ** (FullyUnifiedArray p))
    -- apply (TyFun ts t) | No _ = do
    --     ts' <- traverse apply ts
    --     t' <- apply t
    --     pure (TyFun (fst <$> ts') (fst t') ** (FullyUnifiedFun ts' t'))
    apply x@(TyCon {n=n} name ts) | No _ = do 
        ts' <- traverse apply ts
        pure (TyCon name ts')
        -- pure (TyCon name (fst <$> ts') ** (FullyUnifiedCon name ts'))
    apply (TyVar r) | Yes ItIsTyVar = do 
        let x = TyVar r
        entry <- find x
        case entry.rp of
            Nothing => do 
                warn "uninstantiated type variable `\{show x}` detected; assuming int." pure (TyCon "int" [])
            Just (t ** contra) => do
                b <- state (\s => runIdentity (runStateT s (runEitherT (occursIn {p=ItIsTyVar} (TyVar r) t))))
                if fromEither b then throwError (RecursiveOccurenceErr (TyVar r) t) else do
                    apply t
    apply x@(TyVar _) | No _ impossible

fromTy0: Ty0 -> Either String Ty 
fromTy0 (TyCon "unit" ts {n}) = case ts of [] => pure TyUnit; _ => Left "arity of unit cannot be \{show n}"
fromTy0 (TyCon "int" ts {n}) = case ts of [] => pure TyI32; _ => Left "arity of int cannot be \{show n}"
fromTy0 (TyCon "float" ts {n}) = case ts of [] => pure TyF32; _ => Left "arity of float cannot be \{show n}"
fromTy0 (TyCon "bool" ts {n}) = case ts of [] => pure TyBool; _ => Left "arity of bool cannot be \{show n}"
fromTy0 (TyCon "array" ts {n}) = case ts of [t] => TyArray <$> fromTy0 t; _ => Left "arity of array cannot be \{show n}"
fromTy0 (TyCon "->" ts {n}) = case ts of [t1, t2] => TyFun <$> fromTy0 t1 <*> fromTy0 t2; _ => Left "arity of -> cannot be \{show n}"
fromTy0 (TyCon "tuple" ts {n}) = case ts of (t0::t1::ts) => TyTuple <$> traverse fromTy0 (t0::t1::ts); _ => Left "arity of tuple cannot be \{show n}"
fromTy0 (TyCon name ts {n}) = Left "unknown type constructor: \{name}"
fromTy0 (TyVar _) = pure TyI32
-- fromTy0 (TyCon "int" []) = pure TyI32
-- fromTy0 (TyCon "int" _ {n}) = throwError "arity of int cannot be \{show n}"
-- fromTy0 (TyCon "float" []) = pure TyF32
-- fromTy0 (TyCon "float" _ {n}) = throwError "arity of float cannot be \{show n}"
-- fromTy0 (TyCon "bool" []) = pure TyBool
-- fromTy0 (TyCon "bool" _ {n}) = throwError "arity of bool cannot be \{show n}"
-- fromTy0 (TyCon "array" [t]) = TyArray <$> fromTy0 t
-- fromTy0 (TyCon "array" _ {n}) = throwError "arity of array cannot be \{show n}"
-- fromTy0 (TyCon "->" [t1, t2]) = TyFun <$> fromTy0 t1 <*> fromTy0 t2
-- fromTy0 (TyCon "->" _  {n}) = throwError "arity of -> cannot be \{show n}"
-- fromTy0 (TyCon "tuple" ts {n=S (S _)}) = TyTuple <$> traverse fromTy0 ts
-- fromTy0 (TyCon "tuple" _ {n}) = throwError "arity of tuple cannot be \{show n}"
-- fromTy0 (TyVar _) = pure TyI32
-- fromTy0 (TyUnit ** _) = TyUnit
-- fromTy0 (tI32 ** _) = tI32
-- fromTy0 (tF32 ** _) = tF32
-- fromTy0 (tBool ** _) = tBool
-- fromTy0 (_ ** (FullyUnifiedTuple ts')) = TyTuple (fromTy0 <$> ts')
-- fromTy0 (TyArray t ** (FullyUnifiedArray t')) = TyArray (fromTy0 (t ** t'))
-- fromTy0 (_ ** (FullyUnifiedFun ts' t')) = TyFun (fromTy0 <$> ts') (fromTy0 t')


public export
interface ExtEnvI m where 
    find: (x: NonNullString) -> m (Maybe Ty0)
    extend: (x: NonNullString) -> (t: Ty0) -> m ()
    
export 
MonadState (List (NonNullString, Ty0)) m => ExtEnvI m where
    find x = gets (lookup x)
    extend x t = modify ((x, t)::)

-- export 
-- (Monad m, ExtEnvI m) => ExtEnvI (EitherT e m) where 
--     find x = lift (find x)
--     extend x t = lift (extend x t)

interface TyVarGenI m where
    gen: m Ty0

(Monad m, MonadState Nat m) => TyVarGenI m where
    gen = do 
        r <- get
        modify S
        pure (TyVar r)

data Pred = IsInNum Ty0 | IsInEq Ty0 | IsInOrd Ty0
Show Pred where 
    show (IsInNum t) = "Num \{show t}"
    show (IsInEq t) = "Eq \{show t}"
    show (IsInOrd t) = "Ord \{show t}"

Eq Pred where 
    IsInNum t1 == IsInNum t2 = t1 == t2
    IsInEq t1 == IsInEq t2 = t1 == t2
    IsInOrd t1 == IsInOrd t2 = t1 == t2
    _ == _ = False

record ClassEnv where 
    constructor MkClsEnv
    classes: SortedMap NonNullString (List NonNullString, Ty0)

public export
TypingRes: Type -> Type 
TypingRes a = Either String a

mutual 
    infer: (Info a) => {env: List (NonNullString, Ty0)} -> 
    (expr: Node a) -> 
    RWST String (SortedMap NodeKeyType (List1 (Ty0))) Nat (EitherT UnifyError (StateT UnionFind (StateT (List (NonNullString, Ty0)) Identity))) (List Pred, Ty0)
    infer n = do 
        (preds, t) <- infer_ {env} n `catchError` (\e@(UnifyErr msg t1 t2) => if "when inferring type of" `isPrefixOf` msg then throwError e else throwError (UnifyErr ("when inferring type of `\{show n}`: " ++ msg) t1 t2))
        -- info (show n.getKey.key ++ " :: " ++ show t ++ " :: " ++ show @{a2} n.getKey.span) pure ()
        pass (do pure((preds, t), insert n.getKey.key (t:::[])))

    infer_: (Info a) => {env: List (NonNullString, Ty0)} -> 
    (expr: Node a) -> 
    RWST String (SortedMap NodeKeyType (List1 (Ty0))) Nat (EitherT UnifyError (StateT UnionFind (StateT (List (NonNullString, Ty0)) Identity))) (List Pred, Ty0)
    infer_ U = pure ([], tUnit)
    infer_ (I _) = pure ([], tI32)
    infer_ (B _) = pure ([], tBool)
    infer_ (F _) = pure ([], tF32)
    infer_ (Var {key} x) = do 
        case lookup x env of
            Just t => pure ([], t)
            Nothing => if cast x == "Array.create" || cast x == "Array.make" then do a <- gen; pure ([], tI32 `fn` a `fn` (tArray a)) else case !(lift $ lift $ lift $ find x) of
                Just t => pure ([], t)
                Nothing => do 
                    t <- gen 
                    lift $ lift $ lift $ extend x t
                    warn "free variable `\{x}` assumed as external.\nFile \{!ask}, \{show @{a2} key.span}" pure ()
                    pure ([], t)
    infer_ (Get n1 n2) = do 
        (preds1, t1) <- infer {env} n1
        a <- gen
        lift $ unify t1 (tArray a)
        (preds2, t2) <- infer {env} n2
        lift $ unify t2 tI32
        pure (preds1 ++ preds2, a)
    infer_ (Neg n) = do (ps, t) <- infer {env} n; {-lift $ unify t tI32; -} pure (IsInNum t :: ps, t)
    infer_ (FNeg n) = do (ps, t) <- infer {env} n; lift $ unify t tF32; pure (ps, tF32)
    -- infer_ {env} (App _ [n1]) = do t1 <- infer {env} n1; lift $ unify t1 tBool; pure tBool
    -- infer_ {env} (App _ [n1, n2]) = do
    --     t1 <- infer {env} n1; lift $ unify t1 tI32
    --     t2 <- infer {env} n2
    --     pure (TyArray t2)
    -- infer_ {env} (App n1 [n2] ** WellFormedApp1 n1' n2') = do
    --     t1 <- infer {env} (n1 ** n1')
    --     t2 <- infer {env} (n2 ** n2')
    --     t <- gen
    --     lift $ unify t1 (TyFun [t2] t)
    --     pure t
    infer_ (App f args) = do
        (fpreds, tfunc) <- infer {env} f
        (argpreds, targs) <- unzip <$> traverse (infer {env}) args 
        t <- gen
        lift $ unify tfunc (foldr fn t targs)
        pure (fpreds ++ concat argpreds, t)
    infer_ (FMul n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 tF32; lift $ unify t2 tF32; pure (ps1 ++ ps2, tF32)
    infer_ (FDiv n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 tF32; lift $ unify t2 tF32; pure (ps1 ++ ps2, tF32)
    infer_ (FAdd n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 tF32; lift $ unify t2 tF32; pure (ps1 ++ ps2, tF32)
    infer_ (FSub n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 tF32; lift $ unify t2 tF32; pure (ps1 ++ ps2, tF32)
    infer_ (Add n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; {-lift $ unify t1 tI32; lift $ unify t2 tI32;-} pure (IsInNum t1 :: ps1 ++ ps2, t1)
    infer_ (Sub n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; {-lift $ unify t1 tI32; lift $ unify t2 tI32;-} pure (IsInNum t1 :: ps1 ++ ps2, t1)
    infer_ (Eq n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInEq t1 :: ps1 ++ ps2, tBool)
    infer_ (Neq n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInEq t1 :: ps1 ++ ps2, tBool)
    infer_ (Lt n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInOrd t1 :: ps1 ++ ps2, tBool)
    infer_ (Le n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInOrd t1 :: ps1 ++ ps2, tBool)
    infer_ (Gt n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInOrd t1 :: ps1 ++ ps2, tBool)
    infer_ (Ge n1 n2) = do (ps1, t1) <- infer {env} n1; (ps2, t2) <- infer {env} n2; lift $ unify t1 t2; pure (IsInOrd t1 :: ps1 ++ ps2, tBool)
    infer_ (Tuple ns) = do
        (pss, ts) <- unzip <$> traverse (infer {env}) ns
        pure (concat pss, tTuple ts)
    infer_ (Put n1 n2 n3) = do
        (ps2, t2) <- infer {env} n2; lift $ unify t2 tI32
        (ps3, t3) <- infer {env} n3
        (ps1, t1) <- infer {env} n1; lift $ unify t1 (tArray t3)
        pure (ps1 ++ ps2 ++ ps3, tUnit)
    infer_ (If n1 n2 n3) = do
        (ps1, t1) <- infer {env} n1; lift $ unify t1 tBool
        (ps2, t2) <- infer {env} n2
        (ps3, t3) <- infer {env} n3
        lift $ unify t2 t3
        pure (ps1 ++ ps2 ++ ps3, t2)
    infer_ (Semi n1 n2) = do (ps1, t1) <- infer {env} n1; lift $ unify t1 tUnit; (ps2, t2) <- infer {env} n2; pure (ps1 ++ ps2, t2)
    infer_ (Let x n1 n2) = do (ps1, t1) <- infer {env} n1; t <- gen; lift $ unify t t1; (ps2, t2) <- infer {env=(x, t)::env} n2; pure (ps1 ++ ps2, t2)
    infer_ (LetTuple xs n1 n2) = do
        (ps1, t1) <- infer {env} n1
        ts <- traverse (const gen) xs
        lift $ unify t1 (tTuple ts)
        (ps2, t2) <- infer {env=reverseOnto env (toList (zip xs ts))} n2
        pure (ps1 ++ ps2, t2)
    infer_ (LetRec (MkFunDef fkey name args body) n2) = do
        tname <- gen
        let env = (name, tname)::env
        targs <- traverse (const gen) args
        let env' = reverseOnto env (toList $ zip args targs)
        (psbody, res) <- infer {env = env'} body
        let tfun = foldr fn res targs
        lift $ unify tname tfun
        pass (do pure ((), insert fkey.key (tfun:::[])))
        (ps2, t2) <- infer {env} n2
        pure (psbody ++ ps2, t2)


MonadError e m => MonadError e (EitherT e' m) where
    throwError = lift . throwError
    catchError m f = MkEitherT $ catchError (runEitherT m) (\e => runEitherT (f e))
  

MonadState s m => MonadState s (StateT s' m) where 
  get = lift get
  put = lift . put
  state = lift . state

-- MonadError e m => MonadError e (StateT s m) where
--   throwError = lift . throwError
--   catchError m f = ST $ \s => catchError (runStateT s m) (\e => runStateT s (f e))

-- infer0: (MonadError MergeError m, Monad m, ExtEnvI m, TyVarGenI m, UnifyI m) => Node -> m Ty0
-- infer0 n = pure TyUnit

-- infer1: (MonadError SyntaxError m, MonadError UnifyError m, MonadError MergeError m) => Node -> m Ty0 
-- infer1 n = pure TyUnit

emptyExtEnv: List (String, Ty0)
emptyExtEnv = []

runEitherT': (Monad m) => (0 e: Type) -> EitherT e m a -> m (Either e a)
runEitherT' e m = runEitherT m

-- export 
-- showWithMaybeUnified: (n: Node) -> (m: SortedMap NodeKeyType (List (Ty0))) -> IO ()
-- showWithMaybeUnified n@(Let {key} _ n1 n2) m = do go key n1; go key n2
-- showWithMaybeUnified n@(LetRec {key} (FunDef ) n2) m = do go key n2
-- where
--     go: (Info a) => (key: a) -> Node -> IO ()
--     go key node = do 
--         putStr $ show key.key
--         putStr " "
--         putStr $ show @{a2} key.span
--         putStr " :: "
--         case lookup key.key m of
--             Just t => putStr $ show t
--             Nothing => putStr "???"
--         putStrLn ""
nub: (Eq a) => List1 a -> List1 a
nub (x:::xs) = go (x:::[]) xs
    where
        go: List1 a -> List a -> List1 a
        go acc [] = reverse acc
        go acc (x::xs) = if elem x acc then go acc xs else go (cons x acc) xs

transform: UnionFind -> SortedMap NodeKeyType (List1 Ty0) -> Either String (SortedMap NodeKeyType (List1 Ty))
transform uf m = do 
    let m = traverse (traverse apply) m
    let m = evalStateT uf m
    case m of 
        Left e => Left $ show e
        Right m => traverse (\mm => nub <$> traverse fromTy0 mm) m

checkPred: Pred -> StateT UnionFind (Either String) ()
checkPred (IsInNum t) = do 
    let t = runStateT !get (apply t)
    case t of 
        Left e => throwError $ show e
        Right (uf, t) => do 
            put uf 
            case fromTy0 t of
                Left e => throwError e
                Right t => case t of 
                    TyI32 => pure ()
                    TyF32 => pure ()
                    _ => throwError "Num has no instance for \{show t}" 
checkPred (IsInEq t) = do
    let t = runStateT !get (apply t)
    case t of 
        Left e => throwError $ show e
        Right (uf, t) => do 
            put uf 
            case fromTy0 t of
                Left e => throwError e
                Right t => case t of 
                    TyI32 => pure ()
                    TyF32 => pure ()
                    TyBool => pure ()
                    _ => throwError "Eq has no instance for \{show t}"
checkPred (IsInOrd t) = do
    let t = runStateT !get (apply t)
    case t of 
        Left e => throwError $ show e
        Right (uf, t) => do 
            put uf 
            case fromTy0 t of
                Left e => throwError e
                Right t => case t of 
                    TyI32 => pure ()
                    TyF32 => pure ()
                    _ => throwError "Ord has no instance for \{show t}"

export
infer': (Info a) => {path: String} -> (n: Node a) -> TypingRes (SortedMap NodeKeyType (List1 Ty), List (NonNullString, Ty), Ty)
infer' p = do 
    let extEnv = the (List _) [(MkNonNullStr "not", tBool `fn` tBool)]
    let a = runRWST path Z (infer {env = []} p)
    let a = runEitherT a
    let a = runStateT UnionFind.empty a
    let a = runStateT extEnv a
    let (extEnv, uf, a) = runIdentity a
    case a of 
        Left e => Left $ "\{path}: " ++ show e
        Right ((preds, a), _, a'') => do
            let preds = evalStateT uf (traverse checkPred preds)
            case preds of 
                Left e => Left $ "\{path}: " ++ e 
                Right _ => do
            -- info ("preds: \n" ++ joinBy "\n" (show <$> nub preds)) pure ()
                    let a'' = transform uf a''
                    case a'' of
                        Left e => Left $ "\{path}: " ++ show e
                        Right a'' => do
                            let c = runStateT uf (apply a)
                            case c of 
                                Left e => Left $ "\{path}: " ++ show e
                                Right (uf, a) => case fromTy0 a of
                                    Left e => Left $ "\{path}: " ++ e
                                    Right a => do
                                        let b: Either RecursiveOccurenceError (UnionFind, List Ty0) = runStateT uf (traverse apply (snd <$> extEnv)) 
                                        case b of 
                                            Left e => Left $ "\{path}: " ++ show e
                                            (Right (_, tys)) => do 
                                                let tys: Either String (List Ty) = traverse fromTy0 tys
                                                case tys of
                                                    Left e => Left $ "\{path}: " ++ e 
                                                    Right tys => Right (a'', zip (fst <$> extEnv) tys, a)
            -- let d = runStateT uf (traverse Typing.apply (snd <$> extEnv))
    

    