module Typing
import Ty
import NonNullString
import Info
import Data.Vect
import Data.List
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

data MaybeUnified: Type where
    TyUnit: MaybeUnified
    TyI32: MaybeUnified
    TyF32: MaybeUnified
    TyBool: MaybeUnified
    TyTuple: {n: Nat} -> (ts: Vect (2 + n) MaybeUnified) -> MaybeUnified
    TyArray: (t: MaybeUnified) -> MaybeUnified
    TyFun: {n: Nat} -> (ts: Vect (1 + n) MaybeUnified) -> (t: MaybeUnified) -> MaybeUnified
    TyVar: Nat -> MaybeUnified

Show MaybeUnified where
    show TyUnit = "unit"
    show TyI32 = "int"
    show TyF32 = "float"
    show TyBool = "bool"
    show (TyTuple {n=n} ts) = "(\{", " `joinBy` assert_total show <$> toList ts})"
    show (TyArray t) = show t ++ " array"
    show (TyFun {n=n} ts t) = "(\{", " `joinBy` assert_total show <$> toList ts}) -> \{show t}"
    show (TyVar r) = "'\{show r}"


-- Cast TypeVar MaybeUnified where
--     cast (TyVar r) = TyVar r

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

Ord MaybeUnified where
    compare a b = compare (show a) (show b)

public export 
data UnifyError = UnifyErr String MaybeUnified MaybeUnified

export 
Show UnifyError where
    show (UnifyErr msg t1 t2) = msg ++ "cannot unify `\{show t1}` with `\{show t2}`"

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
    isTyVar t | (TyVar _) = Yes ItIsTyVar
    isTyVar _ | TyUnit = No absurd 
    isTyVar _ | TyI32 = No absurd
    isTyVar _ | TyF32 = No absurd
    isTyVar _ | TyBool = No absurd
    isTyVar _ | TyTuple ts = No absurd
    isTyVar _ | TyArray t = No absurd
    isTyVar _ | TyFun ts t = No absurd

record TypeAnnotated a where 
    constructor MkTypeAnnotated
    node: a 
    ty: MaybeUnified

namespace UnionFind
    data Entry: Type where
        MkEntry: (father: MaybeUnified) -> (rp: Maybe (t: MaybeUnified ** (Not(IsTyVar t)))) -> (rank: Nat) -> Entry
    
    export
    (.father) : Entry -> MaybeUnified
    (.father) (MkEntry father _ _) = father

    export
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
    data MergeError: Type where
        MergeErr: MaybeUnified -> MaybeUnified -> MergeError

    public export
    interface (Monad m) => UnionFindI m where
        find: (t: MaybeUnified) -> StateT UnionFind m Entry
        merge: (t1: MaybeUnified) -> (t2: MaybeUnified) -> {auto 0 p: IsTyVar t1} -> EitherT MergeError (StateT UnionFind m) ()
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
        where uf': List (List1 (MaybeUnified, MaybeUnified))
              uf' = ((\(k, v) => (k, v.father)) <$>) <$> groupAllWith (\(k, v) => (.father) . snd $ runIdentity(runStateT uf (assert_total find k))) (SortedMap.toList uf)

data FullyUnified: MaybeUnified -> Type where
    FullyUnifiedUnit: FullyUnified TyUnit
    FullyUnifiedI32: FullyUnified TyI32
    FullyUnifiedF32: FullyUnified TyF32
    FullyUnifiedBool: FullyUnified TyBool
    FullyUnifiedTuple: (ts: Vect (2 + n) (t: MaybeUnified ** FullyUnified t)) -> FullyUnified (TyTuple (fst <$> ts))
    FullyUnifiedArray: (FullyUnified t) -> FullyUnified (TyArray t)
    FullyUnifiedFun: (ts: Vect (1 + n) (t: MaybeUnified ** FullyUnified t)) -> (t: MaybeUnified ** FullyUnified t) -> FullyUnified (TyFun (fst <$> ts) (fst t))

interface UnifyI m where
    unify: MaybeUnified -> MaybeUnified -> EitherT UnifyError (StateT UnionFind m) ()

(Monad m) => UnifyI m where
    unify t1 t2 = do
        entry1 <- lift $ find t1
        entry2 <- lift $ find t2
        unify' (fromMaybe entry1.father (fst <$> entry1.rp)) (fromMaybe entry2.father (fst <$> entry2.rp))
    where
        unify': (t1: MaybeUnified) -> (t2: MaybeUnified) -> EitherT UnifyError (StateT UnionFind m) ()
        unify' TyUnit TyUnit = pure ()
        unify' TyI32 TyI32 = pure ()
        unify' TyF32 TyF32 = pure ()
        unify' TyBool TyBool = pure ()
        unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) with (decEq n1 n2)
            unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) | (Yes p) = (foldlM (\() => uncurry unify) () (zip ts1 (rewrite p in ts2))) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show tu1}` and `\{show tu2}`: " t1 t2))
            unify' tu1@(TyTuple {n=n1} ts1) tu2@(TyTuple {n=n2} ts2) | (No _) = throwError (UnifyErr "different length tuple type" (TyTuple ts1) (TyTuple ts2))
        unify' (TyArray t1) (TyArray t2) = unify t1 t2
        unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) with (decEq n1 n2)
            unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (Yes p) = foldlM (\() => uncurry unify) !(unify t1 t2) (zip ts1 (rewrite p in ts2)) `catchE` (\(UnifyErr msg t1 t2) => throwError (UnifyErr "when unifying `\{show (TyFun ts1 t1)}` and `\{show (TyFun ts2 t2)}`: " t1 t2))
            unify' (TyFun {n=n1} ts1 t1) (TyFun {n=n2} ts2 t2) | (No p) = throwError (UnifyErr "" (TyFun ts1 t1) (TyFun ts2 t2))
        unify' (TyVar r1) t = merge (TyVar r1) t `catchE` (\(MergeErr t1 t2) => throwError (UnifyErr "when unifying \{show (TyVar r1)} and \{show t}: " t1 t2))
        unify' t (TyVar r2) = merge (TyVar r2) t `catchE` (\(MergeErr t1 t2) => throwError (UnifyErr "when unifying \{show (TyVar r2)} and \{show t}: " t1 t2))
        unify' t1 t2 = throwError (UnifyErr "" t1 t2)

occursIn: (x: MaybeUnified) -> {auto p: IsTyVar x} -> (t: MaybeUnified) -> EitherT Bool (State UnionFind) Bool 
occursIn x TyUnit = pure False
occursIn x TyI32 = pure False
occursIn x TyF32 = pure False
occursIn x TyBool = pure False
occursIn x (TyTuple ts) = do 
    bs <- traverse (occursIn x) ts
    pure (foldl (\acc, b => acc || b) False bs)
occursIn x (TyArray t) =  x `occursIn` t
occursIn x (TyFun ts t) = do 
    bs <- traverse (occursIn x) ts
    b <- x `occursIn` t
    pure (foldl (\acc, b => acc || b) b bs)
occursIn x t@(TyVar x2) = do 
    if x == t then throwError True else do
        entry <- lift $ find t
        case entry.rp of
            Nothing => pure False
            Just (t ** contra) => x `occursIn` t

data RecursiveOccurenceError: Type where
    RecursiveOccurenceErr: (x: MaybeUnified) -> {auto p: IsTyVar x} -> MaybeUnified -> RecursiveOccurenceError

export 
Show RecursiveOccurenceError where
    show (RecursiveOccurenceErr x t) = "recursive occurence of `\{show x}` in `\{show t}`"

apply: (t: MaybeUnified) -> StateT UnionFind (Either RecursiveOccurenceError) (t': MaybeUnified ** FullyUnified t')
apply x with (isTyVar x) proof p
    apply TyUnit | No _ = pure (TyUnit ** FullyUnifiedUnit)
    apply TyI32 | No _ = pure (TyI32 ** FullyUnifiedI32)
    apply TyF32 | No _ = pure (TyF32 ** FullyUnifiedF32)
    apply TyBool | No _ = pure (TyBool ** FullyUnifiedBool)
    apply (TyTuple ts) | No _ = do 
        ts' <- traverse apply ts
        pure (TyTuple (fst <$> ts') ** (FullyUnifiedTuple ts'))
    apply (TyArray t) | No _ = do
        (t' ** p) <- apply t
        pure (TyArray t' ** (FullyUnifiedArray p))
    apply (TyFun ts t) | No _ = do
        ts' <- traverse apply ts
        t' <- apply t
        pure (TyFun (fst <$> ts') (fst t') ** (FullyUnifiedFun ts' t'))
    apply (TyVar r) | Yes ItIsTyVar = do 
        let x = TyVar r
        entry <- find x
        case entry.rp of
            Nothing => do 
                warn "uninstantiated type variable `\{show x}` detected; assuming int." pure (TyI32 ** FullyUnifiedI32)
            Just (t ** contra) => do
                b <- state (\s => runIdentity (runStateT s (runEitherT (occursIn {p=ItIsTyVar} (TyVar r) t))))
                if fromEither b then throwError (RecursiveOccurenceErr (TyVar r) t) else do
                    apply t
    apply x@(TyVar _) | No _ impossible

fromFullyUnified: (t: MaybeUnified ** FullyUnified t) -> Ty 
fromFullyUnified (TyUnit ** _) = TyUnit
fromFullyUnified (TyI32 ** _) = TyI32
fromFullyUnified (TyF32 ** _) = TyF32
fromFullyUnified (TyBool ** _) = TyBool
fromFullyUnified (_ ** (FullyUnifiedTuple ts')) = TyTuple (fromFullyUnified <$> ts')
fromFullyUnified (TyArray t ** (FullyUnifiedArray t')) = TyArray (fromFullyUnified (t ** t'))
fromFullyUnified (_ ** (FullyUnifiedFun ts' t')) = TyFun (fromFullyUnified <$> ts') (fromFullyUnified t')


public export
interface ExtEnvI m where 
    find: (x: NonNullString) -> m (Maybe MaybeUnified)
    extend: (x: NonNullString) -> (t: MaybeUnified) -> m ()
    
export 
MonadState (List (NonNullString, MaybeUnified)) m => ExtEnvI m where
    find x = gets (lookup x)
    extend x t = modify ((x, t)::)

-- export 
-- (Monad m, ExtEnvI m) => ExtEnvI (EitherT e m) where 
--     find x = lift (find x)
--     extend x t = lift (extend x t)

interface TyVarGenI m where
    gen: m MaybeUnified

(Monad m, MonadState Nat m) => TyVarGenI m where
    gen = do 
        r <- get
        modify (+1)
        pure (TyVar r)

-- (Monad m) => TyVarGenI (StateT Nat m) where
--     gen = do 
--         r <- get
--         modify (+1)
--         pure (TyVar r)

-- (Monad m, ExtEnvI m) => ExtEnvI (StateT s m) where
--     find x = lift (find x)
--     extend x t = lift (extend x t)

public export
TypingRes: Type -> Type 
TypingRes a = Either UnifyError (Either RecursiveOccurenceError a)

mutual 
    infer: (Info a) => {env: List (NonNullString, MaybeUnified)} -> 
    (expr: Node a) -> 
    RWST String (SortedMap NodeKeyType (List1 (MaybeUnified))) Nat (EitherT UnifyError (StateT UnionFind (StateT (List (NonNullString, MaybeUnified)) Identity))) MaybeUnified
    infer n = do 
        t <- infer_ {env} n `catchError` (\e@(UnifyErr msg t1 t2) => if "when inferring type of" `isPrefixOf` msg then throwError e else throwError (UnifyErr ("when inferring type of `\{show n}`: " ++ msg) t1 t2))
        -- info (show n.getKey.key ++ " :: " ++ show t ++ " :: " ++ show @{a2} n.getKey.span) pure ()
        pass (do pure(t, insert n.getKey.key (t:::[])))

    infer_: (Info a) => {env: List (NonNullString, MaybeUnified)} -> 
    (expr: Node a) -> 
    RWST String (SortedMap NodeKeyType (List1 (MaybeUnified))) Nat (EitherT UnifyError (StateT UnionFind (StateT (List (NonNullString, MaybeUnified)) Identity))) MaybeUnified
    infer_ U = pure TyUnit
    infer_ (I _) = pure TyI32
    infer_ (B _) = pure TyBool
    infer_ (F _) = pure TyF32
    infer_ {env} (Var {key} x) = do 
        case lookup x env of
            Just t => pure t
            Nothing => if cast x == "Array.create" || cast x == "Array.make" then do a <- gen; pure (TyFun [TyI32, a] (TyArray a)) else case !(lift $ lift $ lift $ find x) of
                Just t => pure t
                Nothing => do 
                    t <- gen 
                    lift $ lift $ lift $ extend x t
                    warn "free variable `\{x}` assumed as external.\nFile \{!ask}, \{show @{a2} key.span}" pure ()
                    pure t
    infer_ {env} (Get n1 n2) = do 
        t1 <- infer {env} (n1)
        a <- gen
        lift $ unify t1 (TyArray a)
        t2 <- infer {env} (n2)
        lift $ unify t2 TyI32
        pure a
    infer_ {env} (Neg n) = do t <- infer {env} (n); lift $ unify t TyI32; pure TyI32
    infer_ {env} (FNeg n) = do t <- infer {env} (n); lift $ unify t TyF32; pure TyF32
    -- infer_ {env} (App _ [n1]) = do t1 <- infer {env} (n1); lift $ unify t1 TyBool; pure TyBool
    -- infer_ {env} (App _ [n1, n2]) = do
    --     t1 <- infer {env} (n1); lift $ unify t1 TyI32
    --     t2 <- infer {env} (n2)
    --     pure (TyArray t2)
    -- infer_ {env} (App n1 [n2] ** WellFormedApp1 n1' n2') = do
    --     t1 <- infer {env} (n1 ** n1')
    --     t2 <- infer {env} (n2 ** n2')
    --     t <- gen
    --     lift $ unify t1 (TyFun [t2] t)
    --     pure t
    infer_ {env} (App f args) = do
        tfunc <- infer {env} f
        targs <- traverse (infer {env}) args
        t <- gen
        lift $ unify tfunc (TyFun targs t)
        pure t
    infer_ {env} (FMul n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyF32; lift $ unify t2 TyF32; pure TyF32
    infer_ {env} (FDiv n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyF32; lift $ unify t2 TyF32; pure TyF32
    infer_ {env} (FAdd n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyF32; lift $ unify t2 TyF32; pure TyF32
    infer_ {env} (FSub n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyF32; lift $ unify t2 TyF32; pure TyF32
    infer_ {env} (Add n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyI32; lift $ unify t2 TyI32; pure TyI32
    infer_ {env} (Sub n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 TyI32; lift $ unify t2 TyI32; pure TyI32
    infer_ {env} (Eq n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Neq n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Lt n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Le n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Gt n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Ge n1 n2) = do t1 <- infer {env} (n1); t2 <- infer {env} (n2); lift $ unify t1 t2; pure TyBool
    infer_ {env} (Tuple ns) = do
        ts <- traverse (infer {env}) ns
        pure (TyTuple ts)
    infer_ {env} (Put n1 n2 n3) = do
        t2 <- infer {env} (n2); lift $ unify t2 TyI32
        ty3 <- infer {env} (n3)
        t1 <- infer {env} (n1); lift $ unify t1 (TyArray ty3)
        pure TyUnit
    infer_ {env} (If n1 n2 n3) = do
        t1 <- infer {env} (n1); lift $ unify t1 TyBool
        t2 <- infer {env} (n2)
        t3 <- infer {env} (n3)
        lift $ unify t2 t3
        pure t2
    infer_ {env} (Semi n1 n2) = do t1 <- infer {env} (n1); lift $ unify t1 TyUnit; infer {env} (n2)
    infer_ {env} (Let x n1 n2) = do t1 <- infer {env} (n1); t <- gen; lift $ unify t t1; infer {env=(x, t)::env} (n2)
    infer_ {env} (LetTuple xs n1 n2) = do
        t1 <- infer {env} (n1)
        ts <- traverse (const gen) xs
        lift $ unify t1 (TyTuple ts)
        infer {env=(reverse $ toList $ zip xs ts) ++ env} (n2)
    infer_ {env} (LetRec (MkFunDef fkey name args body) n2) = do
        tname <- gen
        let env = (name, tname)::env
        targs <- traverse (const gen) args
        let env' = (reverse $ toList $ zip args targs) ++ env
        res <- infer {env = env'} (body)
        let tfun = TyFun targs res
        lift $ unify tname tfun
        pass (do pure ((), insert fkey.key (tfun:::[])))
        infer {env} (n2)


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

-- infer0: (MonadError MergeError m, Monad m, ExtEnvI m, TyVarGenI m, UnifyI m) => Node -> m MaybeUnified
-- infer0 n = pure TyUnit

-- infer1: (MonadError SyntaxError m, MonadError UnifyError m, MonadError MergeError m) => Node -> m MaybeUnified 
-- infer1 n = pure TyUnit

emptyExtEnv: List (String, MaybeUnified)
emptyExtEnv = []

runEitherT': (Monad m) => (0 e: Type) -> EitherT e m a -> m (Either e a)
runEitherT' e m = runEitherT m

-- export 
-- showWithMaybeUnified: (n: Node) -> (m: SortedMap NodeKeyType (List (MaybeUnified))) -> IO ()
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

transform: UnionFind -> SortedMap NodeKeyType (List1 (MaybeUnified)) -> Either RecursiveOccurenceError (SortedMap NodeKeyType (List1 Ty))
transform uf m = do 
    let m = traverse (traverse apply) m
    m <- evalStateT uf m
    pure ((\tys => nub (fromFullyUnified <$> tys)) <$> m)

export
infer': (Info a) => {path: String} -> (n: Node a) -> TypingRes (SortedMap NodeKeyType (List1 Ty), List (NonNullString, Ty), Ty)
infer' p = do 
    let extEnv = the (List _) [(MkNonNullStr "not", TyFun [TyBool] TyBool)]
    let a = runRWST path Z (infer {env = []} p)
    let a = runEitherT a
    let a = runStateT UnionFind.empty a
    let a = runStateT extEnv a
    let (extEnv, uf, a) = runIdentity a
    case a of 
        Left e => Left e 
        Right (a, _, a'') => do
            let a'' = transform uf a''
            case a'' of
                Left e => Right (Left e)
                Right a'' => do
                    let c = runStateT uf (apply a)
                    case c of 
                        Left e => Right (Left e)
                        Right (uf, a) => 
                            let a = fromFullyUnified a in
                            let b = runStateT uf (traverse apply (snd <$> extEnv)) in
                            case b of 
                                Left e => Right (Left e)
                                (Right (_, tys)) => Right (Right (a'', zip (fst <$> extEnv) (fromFullyUnified <$> tys), a))
    -- let d = runStateT uf (traverse Typing.apply (snd <$> extEnv))
    

    