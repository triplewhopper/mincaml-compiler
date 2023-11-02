module Id

import Decidable.Equality

public export
data IdKind = Variable | Temporary | Register | MemoryAddress

Eq IdKind where
    (==) Variable Variable = True
    (==) Temporary Temporary = True
    (==) Register Register = True
    (==) MemoryAddress MemoryAddress = True
    (==) _ _ = False
    (/=) x y = not (x == y)

Ord IdKind where
    compare Variable Variable = EQ
    compare Variable Temporary = LT
    compare Variable Register = LT
    compare Variable MemoryAddress = LT
    compare Temporary Variable = GT
    compare Temporary Temporary = EQ
    compare Temporary Register = LT
    compare Temporary MemoryAddress = LT
    compare Register Variable = GT
    compare Register Temporary = GT
    compare Register Register = EQ
    compare Register MemoryAddress = LT
    compare MemoryAddress Variable = GT
    compare MemoryAddress Temporary = GT
    compare MemoryAddress Register = GT
    compare MemoryAddress MemoryAddress = EQ

mutual
    public export
    data IdName: (k: IdKind) -> Type where
        VarName: (name: String) -> {auto p: (name = "" -> Void)} -> IdName Variable
        TmpName: (idx: Nat) -> IdName Temporary
        RegName: (idx: Nat) -> IdName Register
        MemName: (offset: Int) -> (base: IdName Register) -> IdName MemoryAddress

    public export
    data Id : Type where
        MkId: {k: IdKind} -> (IdName k) -> Id
    public export
    data IsKind: Id -> IdKind -> Type where
        IdIsKind: (x: IdName k) -> IsKind (MkId x) k
    -- public export
    -- data IsVar: Id -> Type where
    --     IdIsVar: {auto p: (name =  "" -> Void)} -> IsVar (MkId (VarName name))
    -- public export
    -- data IsTmp: Id -> Type where
    --     IdIsTmp: IsTmp (MkId (TmpName idx))
    -- public export
    -- data IsReg: Id -> Type where
    --     IdIsReg: IsReg (MkId (RegName idx))
    -- public export
    -- data IsMem: Id -> Type where
    --     IdIsMem: IsMem (MkId (MemName offset base))

%hint 
public export
Lemma1: {name: String} -> {auto p: (name = "" -> Void)} -> MkId (VarName name) = x -> IsKind x Variable
Lemma1 {name} Refl = IdIsKind (VarName name)
%hint
public export
Lemma2: {idx: Nat} -> MkId (TmpName idx) = x -> IsKind x Temporary
Lemma2 {idx} Refl = IdIsKind (TmpName idx)
%hint
public export
Lemma3: {idx: Nat} -> MkId (RegName idx) = x -> IsKind x Register
Lemma3 {idx} Refl = IdIsKind (RegName idx)
%hint
public export
Lemma4: {offset: Int} -> {base: IdName Register} -> MkId (MemName offset base) = x -> IsKind x MemoryAddress
Lemma4 {offset} {base} Refl = IdIsKind (MemName offset base)

%hint
public export
Lemma5: x = y -> y = x
Lemma5 Refl = Refl

export
(.kind): Id -> IdKind
(.kind) (MkId {k} _) = k

export
(.name): Id -> String
(.name) (MkId (VarName name)) = name
(.name) (MkId (TmpName idx)) = "__t%" ++ show idx
(.name) (MkId (RegName idx)) = "%" ++ show idx
(.name) (MkId (MemName offset (RegName idx))) = "\{show offset}(%%\{show idx})"

VariableNotTemporary: Variable = Temporary -> Void
VariableNotTemporary Refl impossible
VariableNotRegister: Variable = Register -> Void
VariableNotRegister Refl impossible
VariableNotMemoryAddress: Variable = MemoryAddress -> Void
VariableNotMemoryAddress Refl impossible
TemporaryNotRegister: Temporary = Register -> Void
TemporaryNotRegister Refl impossible
TemporaryNotMemoryAddress: Temporary = MemoryAddress -> Void
TemporaryNotMemoryAddress Refl impossible
RegisterNotMemoryAddress: Register = MemoryAddress -> Void
RegisterNotMemoryAddress Refl impossible

DecEq IdKind where
    decEq Variable Variable = Yes Refl
    decEq Variable Temporary = No VariableNotTemporary
    decEq Variable Register = No VariableNotRegister
    decEq Variable MemoryAddress = No VariableNotMemoryAddress
    decEq Temporary Variable = No (negEqSym VariableNotTemporary)
    decEq Temporary Temporary = Yes Refl
    decEq Temporary Register = No TemporaryNotRegister
    decEq Temporary MemoryAddress = No TemporaryNotMemoryAddress
    decEq Register Variable = No (negEqSym VariableNotRegister)
    decEq Register Temporary = No (negEqSym TemporaryNotRegister)
    decEq Register Register = Yes Refl
    decEq Register MemoryAddress = No RegisterNotMemoryAddress
    decEq MemoryAddress Variable = No (negEqSym VariableNotMemoryAddress)
    decEq MemoryAddress Temporary = No (negEqSym TemporaryNotMemoryAddress)
    decEq MemoryAddress Register = No (negEqSym RegisterNotMemoryAddress)
    decEq MemoryAddress MemoryAddress = Yes Refl

export
Eq Id where
    (==) (MkId (VarName n1)) (MkId (VarName n2)) = n1 == n2
    (==) (MkId (TmpName n1)) (MkId (TmpName n2)) = n1 == n2
    (==) (MkId (RegName n1)) (MkId (RegName n2)) = n1 == n2
    (==) (MkId (MemName o1 (RegName r1))) (MkId (MemName o2 (RegName r2))) = o1 == o2 && r1 == r2
    (==) _ _ = False
    (/=) x y = not (x == y)

export
Ord Id where
    compare (MkId (VarName n1)) (MkId (VarName n2)) = compare n1 n2
    compare (MkId (TmpName n1)) (MkId (TmpName n2)) = compare n1 n2
    compare (MkId (RegName n1)) (MkId (RegName n2)) = compare n1 n2
    compare (MkId (MemName o1 (RegName r1))) (MkId (MemName o2 (RegName r2))) = case compare o1 o2 of
        EQ => compare r1 r2
        other => other
    compare (MkId {k = k1} _) (MkId {k = k2} _) = compare k1 k2


-- check: String -> IdKind -> Bool
-- check "" _ = False
-- check name Variable = not (String.isPrefixOf "%" name) && not (String.isPrefixOf "min_caml_" name)
-- check name Register = String.isPrefixOf "%" name
-- check name MemoryAddress = String.isPrefixOf "min_caml_" name
-- check name Temporary = String.isPrefixOf "__t%" name

MkTmpWithPrf: (idx: Nat) -> (x: Id ** x.kind = Temporary)
MkTmpWithPrf idx = ((MkId (TmpName idx)) ** Refl)