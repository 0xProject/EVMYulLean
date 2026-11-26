import Mathlib.Data.Nat.Log

import EvmYul.EVM.State
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace EVM

/-
Appendix G. Fee Schedule
-/

namespace InstructionGasGroups

def Wzero : List (Operation .EVM) := [.STOP, .RETURN, .REVERT]

def Wbase : List (Operation .EVM) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .BLOBBASEFEE, .PUSH0]

def Wverylow : List (Operation .EVM) := [
  .ADD, .SUB, .NOT, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR,
  .CALLDATALOAD, .MLOAD, .MSTORE, .MSTORE8
  ] ++ pushInstrsWithoutZero
    ++ dupInstrs
    ++ swapInstrs
  where
    pushInstrsWithoutZero : List (Operation .EVM) := [
      .PUSH1, .PUSH2, .PUSH3, .PUSH4, .PUSH5,
      .PUSH6, .PUSH7, .PUSH8, .PUSH9, .PUSH10,
      .PUSH11, .PUSH12, .PUSH13, .PUSH14, .PUSH15,
      .PUSH16, .PUSH17, .PUSH18, .PUSH19, .PUSH20,
      .PUSH21, .PUSH22, .PUSH23, .PUSH24, .PUSH25,
      .PUSH26, .PUSH27, .PUSH28, .PUSH29, .PUSH30,
      .PUSH31, .PUSH32
    ]
    dupInstrs : List (Operation .EVM) := [
      .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
      .DUP6, .DUP7, .DUP8, .DUP9, .DUP10,
      .DUP11, .DUP12, .DUP13, .DUP14, .DUP15,
      .DUP16
    ]
    swapInstrs : List (Operation .EVM) := [
      .SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5,
      .SWAP6, .SWAP7, .SWAP8, .SWAP9, .SWAP10,
      .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15,
      .SWAP16
    ]

def Wlow : List (Operation .EVM) := [
  .MUL, .DIV, .SDIV, .MOD, .SMOD, .SIGNEXTEND, .SELFBALANCE, .CLZ
]

def Wmid : List (Operation .EVM) := [
  .ADDMOD, .MULMOD, .JUMP
]

def Whigh : List (Operation .EVM) := [
  .JUMPI
]

def Wcopy : List (Operation .EVM) := [
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY
]

def Wcall : List (Operation .EVM) := [
  .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL
]

def Wextaccount : List (Operation .EVM) := [
  .BALANCE, .EXTCODESIZE, .EXTCODEHASH
]

end InstructionGasGroups

section Gas

open GasConstants InstructionGasGroups

/-- Ethereum execution-layer hard forks supported by the `EVMYulLean 2.0` gas and semantics model. -/
inductive Fork where
  | Frontier
  | Homestead
  | TangerineWhistle
  | SpuriousDragon
  | Byzantium
  | Constantinople
  | Istanbul
  | Berlin
  | London
  | Paris
  | Shanghai
  | Cancun
  | Prague
  | Osaka
  deriving DecidableEq, Repr, BEq, Inhabited

namespace Fork

/-- True when EIP-2929 warm/cold storage & account access rules apply (`Berlin` and later). -/
def hasEIP2929 : Fork → Bool
  | .Frontier | .Homestead | .TangerineWhistle | .SpuriousDragon
  | .Byzantium | .Constantinople | .Istanbul => false
  | _ => true

/-- True when EIP-7623 calldata floor gas applies (`Prague` and `Osaka`). -/
def hasEIP7623 : Fork → Bool
  | .Prague | .Osaka => true
  | _ => false

end Fork

/--
(328)
-/
def Cₘ (a : UInt256) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

/-- Pure, total, stack-safe EIP-2200 / EIP-2929 / EIP-3529 `SSTORE` gas cost function
    parameterized by `Fork` and explicit typed operands `(v₀, v, v', isWarm)`. -/
def CsstorePure (fork : Fork := .Cancun) (v₀ v v' : UInt256) (isWarm : Bool) : ℕ :=
  let loadComponent :=
    if !fork.hasEIP2929 || isWarm then 0 else Gcoldsload
  let storeComponent :=
    if v = v' || v₀ ≠ v             then Gwarmaccess else
    if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else
    /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  loadComponent + storeComponent

/-- Total, stack-safe `SSTORE` gas cost on `EVM.State` with zero partial (`!`) accesses. -/
def Csstore (s : EVM.State) (fork : Fork := .Cancun) : ℕ :=
  let { stack := μₛ, accountMap := σ, σ₀ := σ₀, executionEnv.codeOwner := Iₐ, .. } := s
  let storeAddr : UInt256 := μₛ[0]?.getD ⟨0⟩
  let v' : UInt256 := μₛ[1]?.getD ⟨0⟩
  let v₀ : UInt256 :=
    match σ₀.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD storeAddr ⟨0⟩
  let v : UInt256 :=
    match σ.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD storeAddr ⟨0⟩
  let isWarm := s.substate.accessedStorageKeys.contains (Iₐ, storeAddr)
  CsstorePure fork v₀ v v' isWarm

def Ctstore : ℕ :=
  let loadComponent := 0
  let storeComponent := Gwarmaccess
  loadComponent + storeComponent

/--
(328)
-/
def Caccess (a : AccountAddress) (A : Substate) : ℕ :=
  if A.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

/-- Pure, total, stack-safe `SELFDESTRUCT` gas cost parameterized by `Fork` and typed booleans. -/
def CselfdestructPure (_fork : Fork := .Cancun) (isWarm : Bool) (isDeadTarget : Bool) (hasNonZeroBalance : Bool) : ℕ :=
  let c_cold := if isWarm then 0 else Gcoldaccountaccess
  let c_new := if isDeadTarget && hasNonZeroBalance then Gnewaccount else 0
  Gselfdestruct + c_cold + c_new

/-- Total, stack-safe `SELFDESTRUCT` gas cost on `EVM.State` with zero partial (`!`) accesses. -/
def Cselfdestruct (s : EVM.State) (fork : Fork := .Cancun) : ℕ :=
  let r := AccountAddress.ofUInt256 (s.stack[0]?.getD (⟨0⟩ : UInt256))
  let { substate.accessedAccounts := Aₐ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let isWarm := Aₐ.contains r
  let isDeadTarget := decide (State.dead σ r)
  let hasNonZeroBalance : Bool := (σ.get? Iₐ |>.option (⟨0⟩ : UInt256) (·.balance)) != (⟨0⟩ : UInt256)
  CselfdestructPure fork isWarm isDeadTarget hasNonZeroBalance

/-- Pure, total, stack-safe `SLOAD` gas cost parameterized by `Fork` and `isWarm`. -/
def CsloadPure (fork : Fork := .Cancun) (isWarm : Bool) : ℕ :=
  if !fork.hasEIP2929 || isWarm then Gwarmaccess else Gcoldsload

/-- Total, stack-safe `SLOAD` gas cost with zero partial (`!`) accesses. -/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) (fork : Fork := .Cancun) : ℕ :=
  let slot := μₛ[0]?.getD ⟨0⟩
  CsloadPure fork (A.accessedStorageKeys.contains (I.codeOwner, slot))

def Ctload : ℕ :=
  Gwarmaccess

/--
(331)
-/
def L (n : ℕ) : ℕ := n - (n / 64)

def Cnew (t : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) : ℕ :=
  if EvmYul.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

def Cxfer (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then Gcallvalue else 0

def Cextra (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  Caccess t A + Cxfer val + Cnew r val σ

def Cgascap (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) :=
  if μ.gasAvailable.toNat >= Cextra t r val σ A then
    min (L <| (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat
  else
    g.toNat

def Ccallgas (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  if val = ⟨0⟩ then Cgascap t r val g σ μ A
  else Cgascap t r val g σ μ A + GasConstants.Gcallstipend

/--
NB Assumes stack coherence.
-/
def Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  Cgascap t r val g σ μ A + Cextra t r val σ A

/--
(65)
-/
def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

/-- Pure, total typed operand gas helpers shared between `.EVM` and `.Yul`. -/
def CexpPure (exponent : UInt256) : ℕ :=
  if exponent == ⟨0⟩ then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 exponent.toNat)

def Ckeccak256Pure (size : UInt256) : ℕ :=
  Gkeccak256 + Gkeccak256word * ((size.toNat + 31) / 32)

def CcopyPure (size : UInt256) : ℕ :=
  Gverylow + Gcopy * ((size.toNat + 31) / 32)

def ClogPure (numTopics : ℕ) (dataSize : UInt256) : ℕ :=
  Glog + Glogdata * dataSize.toNat + numTopics * Glogtopic

/-- Fork-aware transaction intrinsic gas (including EIP-7623 calldata floor gas on Prague/Osaka). -/
def intrinsicGas (T : Transaction) (fork : Fork := .Cancun) : ℕ :=
  let (zeroBytes, nonZeroBytes) :=
    T.base.data.foldl
      (λ (z, nz) b ↦ if b == 0 then (z + 1, nz) else (z, nz + 1))
      (0, 0)
  let g₀_data := zeroBytes * GasConstants.Gtxdatazero + nonZeroBytes * GasConstants.Gtxdatanonzero
  let g₀_create : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + R (T.base.data.size)
    else 0
  let g₀_accessList : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  let standardGas := g₀_data + g₀_create + GasConstants.Gtransaction + g₀_accessList
  if fork.hasEIP7623 then
    let tokensInCalldata := zeroBytes + 4 * nonZeroBytes
    let floorGas := GasConstants.Gtransaction + 10 * tokensInCalldata
    max standardGas floorGas
  else
    standardGas

/--
H.1. Gas Cost - the third summand.
Total, stack-safe formulation parameterized by `Fork` with zero partial (`!`) indexing.
-/
def C' (s : State) (instr : Operation .EVM) (fork : Fork := .Cancun) : ℕ :=
  let { accountMap := σ, stack := μₛ, substate := A, toMachineState := μ, executionEnv := I, ..} := s
  let s0 := μₛ[0]?.getD ⟨0⟩
  let s1 := μₛ[1]?.getD ⟨0⟩
  let s2 := μₛ[2]?.getD ⟨0⟩
  let s3 := μₛ[3]?.getD ⟨0⟩
  match instr with
    | .SSTORE => Csstore s fork
    | .TSTORE => Ctstore
    | .EXP => CexpPure s1
    | .EXTCODECOPY => Caccess (AccountAddress.ofUInt256 s0) A + Gcopy * ((s3.toNat + 31) / 32)
    | .LOG0 => ClogPure 0 s1
    | .LOG1 => ClogPure 1 s1
    | .LOG2 => ClogPure 2 s1
    | .LOG3 => ClogPure 3 s1
    | .LOG4 => ClogPure 4 s1
    | .SELFDESTRUCT => Cselfdestruct s fork
    | .CREATE => Gcreate + R s2.toNat
    | .CREATE2 => Gcreate + Gkeccak256word * ((s2.toNat + 31) / 32) + R s2.toNat
    | .KECCAK256 => Ckeccak256Pure s1
    | .JUMPDEST => Gjumpdest
    | .SLOAD => Csload μₛ A I fork
    | .TLOAD => Ctload
    | .BLOCKHASH => Gblockhash
    | .CALL =>         Ccall (AccountAddress.ofUInt256 s1) (AccountAddress.ofUInt256 s1) s2 s0 σ μ A
    | .CALLCODE =>     Ccall (AccountAddress.ofUInt256 s1)          s.executionEnv.codeOwner s2 s0 σ μ A
    | .DELEGATECALL => Ccall (AccountAddress.ofUInt256 s1)          s.executionEnv.codeOwner ⟨0⟩ s0 σ μ A
    | .STATICCALL =>   Ccall (AccountAddress.ofUInt256 s1) (AccountAddress.ofUInt256 s1)    ⟨0⟩ s0 σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then CcopyPure s2 else
      if w ∈ Wextaccount then Caccess (AccountAddress.ofUInt256 s0) A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      0

/-- Pure, total memory expansion cost helper over explicit `(offset, size)` regions. -/
def memoryExpansionWordsPure (activeWords : ℕ) (regions : List (ℕ × ℕ)) : ℕ :=
  regions.foldl (fun acc (off, sz) => MachineState.M acc off sz) activeWords

def memoryExpansionCostPure (activeWords : UInt256) (regions : List (ℕ × ℕ)) : ℕ :=
  let nextWords : UInt256 := .ofNat (memoryExpansionWordsPure activeWords.toNat regions)
  Cₘ nextWords - Cₘ activeWords

/--
H.1. Gas Cost — Total, stack-safe memory expansion cost with zero partial (`!`) indexing.
-/
def memoryExpansionCost (s : EVM.State) (instr : Operation .EVM) : ℕ :=
  Cₘ μᵢ' - Cₘ s.toMachineState.activeWords
 where
  μᵢ' : UInt256 :=
    let aw := s.toMachineState.activeWords.toNat
    let s0 := (s.stack[0]?.getD (⟨0⟩ : UInt256)).toNat
    let s1 := (s.stack[1]?.getD (⟨0⟩ : UInt256)).toNat
    let s2 := (s.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
    let s3 := (s.stack[3]?.getD (⟨0⟩ : UInt256)).toNat
    let s4 := (s.stack[4]?.getD (⟨0⟩ : UInt256)).toNat
    let s5 := (s.stack[5]?.getD (⟨0⟩ : UInt256)).toNat
    let s6 := (s.stack[6]?.getD (⟨0⟩ : UInt256)).toNat
    match instr with
      | .KECCAK256 => .ofNat <| MachineState.M aw s0 s1
      | .CALLDATACOPY | .CODECOPY => .ofNat <| MachineState.M aw s0 s2
      | .MCOPY => .ofNat <| MachineState.M aw (max s0 s1) s2
      | .EXTCODECOPY => .ofNat <| MachineState.M aw s1 s3
      | .RETURNDATACOPY => .ofNat <| MachineState.M aw s0 s2
      | .MLOAD | .MSTORE => .ofNat <| MachineState.M aw s0 32
      | .MSTORE8 => .ofNat <| MachineState.M aw s0 1
      | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
        .ofNat <| MachineState.M aw s0 s1
      | .CREATE | .CREATE2 => .ofNat <| MachineState.M aw s1 s2
      | .CALL | .CALLCODE =>
        let m : ℕ := MachineState.M aw s3 s4
        .ofNat <| MachineState.M m s5 s6
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ := MachineState.M aw s2 s3
        .ofNat <| MachineState.M m s4 s5
      | .RETURN | .REVERT => .ofNat <| MachineState.M aw s0 s1
      | _ => s.toMachineState.activeWords

example (s : EVM.State) : C' s .CLZ = 5 := by rfl

theorem csloadPure_pos (fork : Fork) (isWarm : Bool) : 0 < CsloadPure fork isWarm := by
  unfold CsloadPure Gwarmaccess Gcoldsload
  split <;> decide

theorem cexpPure_ge_gexp (exponent : UInt256) : Gexp ≤ CexpPure exponent := by
  unfold CexpPure
  split <;> omega

end Gas

end EVM

end EvmYul
