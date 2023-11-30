module Asm 

import Id 
import Data.Fin

data CallingConvention = Caller | Callee | NA 


data ABIReg: CallingConvention -> Type where 
    Zero: ABIReg NA
    Ra: ABIReg Caller
    Sp: ABIReg Callee
    Gp: ABIReg NA
    Tp: ABIReg NA
    T: (i: Fin 7) -> ABIReg Caller
    S: (i: Fin 12) -> ABIReg Callee
    A: (i: Fin 8) -> ABIReg Caller

Eq (ABIReg a) where 
    Zero == Zero = True
    Ra == Ra = True
    Sp == Sp = True
    Gp == Gp = True
    Tp == Tp = True
    (T i) == (T j) = i == j
    (S i) == (S j) = i == j
    (A i) == (A j) = i == j
    _ == _ = False
    

data ABIFloatReg: CallingConvention -> Type where 
    Fa: (i: Fin 8) -> ABIFloatReg Caller
    Ft: (i: Fin 12) -> ABIFloatReg Caller 
    Fs: (i: Fin 12) -> ABIFloatReg Callee

data Pseudo: Type where 
    La: (rd: ABIReg a) -> (label: Id) -> Pseudo
