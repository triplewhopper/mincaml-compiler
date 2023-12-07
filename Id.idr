module Id

import Decidable.Equality
import Data.So
import Data.Maybe
import NonNullString
import Info
import Control.Function

public export
data IdKind = Variable | Temporary {-| Register | MemoryAddress-}

Eq IdKind where
    (==) Variable Variable = True
    (==) Temporary Temporary = True
    -- (==) Register Register = True
    -- (==) MemoryAddress MemoryAddress = True
    (==) _ _ = False
    (/=) x y = not (x == y)

Ord IdKind where
    compare Variable Variable = EQ
    compare Variable Temporary = LT
    -- compare Variable Register = LT
    -- compare Variable MemoryAddress = LT
    compare Temporary Variable = GT
    compare Temporary Temporary = EQ
    -- compare Temporary Register = LT
    -- compare Temporary MemoryAddress = LT
    -- compare Register Variable = GT
    -- compare Register Temporary = GT
    -- compare Register Register = EQ
    -- compare Register MemoryAddress = LT
    -- compare MemoryAddress Variable = GT
    -- compare MemoryAddress Temporary = GT
    -- compare MemoryAddress Register = GT
    -- compare MemoryAddress MemoryAddress = EQ

public export
data IdName: (k: IdKind) -> Type where
    VarName: (name: NonNullString) -> NodeKeyType -> IdName Variable
    ExtName: (name: NonNullString) -> IdName Variable
    TmpName: (idx: Nat) -> IdName Temporary
    -- RegName: (idx: Nat) -> IdName Register
    -- MemName: (offset: Int) -> (base: IdName Register) -> IdName MemoryAddress

public export
data Id : Type where
    MkId: {k: IdKind} -> (IdName k) -> Id

public export 
data Label: Type where
    MkLabel: IdName Variable -> Label
    
public export
data IsKind: Id -> IdKind -> Type where
    IdIsKind: (x: IdName k) -> IsKind (MkId x) k

public export 
data IsVarName: IdName Variable -> Type where
    IdIsVarName: (x: NonNullString) -> (idx: NodeKeyType) -> IsVarName (VarName x idx)

public export 
data IsExtName: Id -> Type where
    IdIsExtName: (x: NonNullString) -> IsExtName (MkId (ExtName x))
-- %hint
-- public export
-- varIsNotExt: {x: NonNullString} -> {idx: NodeKeyType} -> VarName x idx = y -> IsExt y -> Void
-- varIsNotExt {x} {idx} Refl (IdIsExt y) impossible

-- %hint 
-- public export
-- tmpIsNotExt: {idx: Nat} -> MkId (TmpName idx) = y -> IsExt y -> Void
-- tmpIsNotExt {idx} Refl (IdIsExt y) impossible

-- %hint 
-- public export
-- extMustBeExt: {x: NonNullString} -> {y: IdName Variable} -> ExtName x = y -> IsExt y
-- extMustBeExt {x} Refl = IdIsExt x

-- %hint
-- public export
-- extNotBeExtImpossible: {x: NonNullString} -> {y: IdName Variable} -> ExtName x = y -> IsExt y -> Void
-- extNotBeExtImpossible {x} {y} Refl (IdIsExt y) impossible

export
fromVariable: (x: Id) -> {auto p: IsKind x Variable} -> IdName Variable
fromVariable (MkId x) {p=IdIsKind x} = x

%hint 
public export
Lemma1: {name: NonNullString} -> {idx: NodeKeyType} -> MkId (VarName name idx) = x -> IsKind x Variable
Lemma1 {name} Refl = IdIsKind (VarName name idx)
%hint 
public export
Lemma2: {name: NonNullString} -> MkId (ExtName name) = x -> IsKind x Variable
Lemma2 {name} Refl = IdIsKind (ExtName name)
%hint
public export
Lemma3: {idx: Nat} -> MkId (TmpName idx) = x -> IsKind x Temporary
Lemma3 {idx} Refl = IdIsKind (TmpName idx)
-- %hint
-- public export
-- Lemma4: {idx: Nat} -> MkId (RegName idx) = x -> IsKind x Register
-- Lemma4 {idx} Refl = IdIsKind (RegName idx)
-- %hint
-- public export
-- Lemma5: {offset: Int} -> {base: IdName Register} -> MkId (MemName offset base) = x -> IsKind x MemoryAddress
-- Lemma5 {offset} {base} Refl = IdIsKind (MemName offset base)

export
(.kind): Id -> IdKind
(.kind) (MkId {k} _) = k

export
(.name): Id -> String
(.name) (MkId (VarName (MkNonNullStr name) _)) = name
(.name) (MkId (ExtName (MkNonNullStr name))) = name
(.name) (MkId (TmpName idx)) = "__t%" ++ show idx
-- (.name) (MkId (RegName idx)) = "%" ++ show idx
-- (.name) (MkId (MemName offset (RegName idx))) = "\{show offset}(%%\{show idx})"

VariableNotTemporary: Variable = Temporary -> Void
VariableNotTemporary Refl impossible
-- VariableNotRegister: Variable = Register -> Void
-- VariableNotRegister Refl impossible
-- VariableNotMemoryAddress: Variable = MemoryAddress -> Void
-- VariableNotMemoryAddress Refl impossible
-- TemporaryNotRegister: Temporary = Register -> Void
-- TemporaryNotRegister Refl impossible
-- TemporaryNotMemoryAddress: Temporary = MemoryAddress -> Void
-- TemporaryNotMemoryAddress Refl impossible
-- RegisterNotMemoryAddress: Register = MemoryAddress -> Void
-- RegisterNotMemoryAddress Refl impossible

export
DecEq IdKind where
    decEq Variable Variable = Yes Refl
    decEq Variable Temporary = No VariableNotTemporary
    -- decEq Variable Register = No VariableNotRegister
    -- decEq Variable MemoryAddress = No VariableNotMemoryAddress
    decEq Temporary Variable = No (negEqSym VariableNotTemporary)
    decEq Temporary Temporary = Yes Refl
    -- decEq Temporary Register = No TemporaryNotRegister
    -- decEq Temporary MemoryAddress = No TemporaryNotMemoryAddress
    -- decEq Register Variable = No (negEqSym VariableNotRegister)
    -- decEq Register Temporary = No (negEqSym TemporaryNotRegister)
    -- decEq Register Register = Yes Refl
    -- decEq Register MemoryAddress = No RegisterNotMemoryAddress
    -- decEq MemoryAddress Variable = No (negEqSym VariableNotMemoryAddress)
    -- decEq MemoryAddress Temporary = No (negEqSym TemporaryNotMemoryAddress)
    -- decEq MemoryAddress Register = No (negEqSym RegisterNotMemoryAddress)
    -- decEq MemoryAddress MemoryAddress = Yes Refl

export
Eq Id where
    (==) (MkId (VarName n1 i1)) (MkId (VarName n2 i2)) = n1 == n2 && i1 == i2
    (==) (MkId (ExtName n1)) (MkId (ExtName n2)) = n1 == n2
    (==) (MkId (TmpName n1)) (MkId (TmpName n2)) = n1 == n2
    -- (==) (MkId (RegName n1)) (MkId (RegName n2)) = n1 == n2
    -- (==) (MkId (MemName o1 (RegName r1))) (MkId (MemName o2 (RegName r2))) = o1 == o2 && r1 == r2
    (==) _ _ = False
    (/=) x y = not (x == y)

export
Ord Id where
    compare (MkId (VarName n1 i1)) (MkId (VarName n2 i2)) = compare (n1, i1) (n2, i2)
    compare (MkId (ExtName n1)) (MkId (ExtName n2)) = compare n1 n2
    compare (MkId (TmpName n1)) (MkId (TmpName n2)) = compare n1 n2
    -- compare (MkId (RegName n1)) (MkId (RegName n2)) = compare n1 n2
    -- compare (MkId (MemName o1 (RegName r1))) (MkId (MemName o2 (RegName r2))) = case compare o1 o2 of
        -- EQ => compare r1 r2
        -- other => other
    compare (MkId {k = k1} _) (MkId {k = k2} _) = compare k1 k2

||| if two variables of type Id are identical, then their kinds are identical
idEqkEq: {k1: IdKind} -> {k2: IdKind} -> {idname1: IdName k1} -> {idname2: IdName k2} -> MkId idname1 = MkId idname2 -> k1 = k2
idEqkEq Refl = Refl

Biinjective VarName where
    biinjective Refl = (Refl, Refl)

Injective ExtName where
    injective Refl = Refl

Injective TmpName where
    injective Refl = Refl

-- Injective RegName where
--     injective Refl = Refl

-- Biinjective MemName where
--     biinjective Refl = (Refl, Refl)

varNameNotEqExtName: VarName name idx = ExtName name' -> Void
varNameNotEqExtName Refl impossible

export 
Eq (IdName Variable) where 
    (==) (VarName name1 idx1) (VarName name2 idx2) = idx1 == idx2 && name1 == name2
    (==) (ExtName name1) (ExtName name2) = name1 == name2
    (==) (VarName _ _) (ExtName _) = False
    (==) (ExtName _) (VarName _ _) = False

export 
Ord (IdName Variable) where
    compare (VarName n1 i1) (VarName n2 i2) = compare (n1, i1) (n2, i2)
    compare (ExtName n1) (ExtName n2) = compare n1 n2
    compare (VarName _ _) (ExtName _) = LT
    compare (ExtName _) (VarName _ _) = GT

export 
Eq (IdName Temporary) where 
    (==) (TmpName idx1) (TmpName idx2) = idx1 == idx2

export 
DecEq (IdName Variable) where 
    decEq (VarName name1 idx1) (VarName name2 idx2) = decEqCong2 (decEq name1 name2) (decEq idx1 idx2)
    decEq (ExtName name1) (ExtName name2) = decEqCong (decEq name1 name2)
    decEq (VarName _ _) (ExtName _) = No varNameNotEqExtName
    decEq (ExtName _) (VarName _ _) = No (negEqSym varNameNotEqExtName)

export 
DecEq (IdName Temporary) where 
    decEq (TmpName idx1) (TmpName idx2) = decEqCong (decEq idx1 idx2)

-- export 
-- DecEq (IdName Register) where 
--     decEq (RegName idx1) (RegName idx2) = decEqCong (decEq idx1 idx2)

-- export 
-- DecEq (IdName MemoryAddress) where 
--     decEq (MemName offset1 base1) (MemName offset2 base2) = decEqCong2 (decEq offset1 offset2) (decEq base1 base2)

export 
DecEq Id where 
    decEq (MkId {k=k1} idname) (MkId {k=k2} idname') with (decEq k1 k2)
        decEq (MkId idname) (MkId idname') | Yes k1Eqk2 = ?d
        decEq (MkId idname) (MkId idname') | No contra = No (\x => contra (idEqkEq x))

export 
Show (IdName Variable) where 
    show (VarName (MkNonNullStr name) idx) = name ++ "'\{show idx}"
    show (ExtName (MkNonNullStr name)) = name
export
Interpolation (IdName Variable) where
    interpolate = show
export
Show (IdName Temporary) where 
    show (TmpName idx) = "__tmp'" ++ show idx
export
Interpolation (IdName Temporary) where
    interpolate = show
export
Show Id where 
    show (MkId (VarName (MkNonNullStr name) idx)) = name ++ "'\{show idx}"
    show (MkId (ExtName (MkNonNullStr name))) = name
    show (MkId (TmpName idx)) = "__tmp'\{show idx}"
    -- show (MkId (RegName idx)) = "__reg'\{show idx}"
    -- show (MkId (MemName offset (RegName idx))) = "\{show offset}(%%\{show idx})"

export
Interpolation Id where
    interpolate id = show id

MkTmpWithPrf: (idx: Nat) -> (x: Id ** x.kind = Temporary)
MkTmpWithPrf idx = ((MkId (TmpName idx)) ** Refl)