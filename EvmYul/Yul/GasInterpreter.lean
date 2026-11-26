import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Yul.Exception
import EvmYul.EVM.Gas
import EvmYul.Operations

namespace EvmYul

namespace Yul

open EvmYul.EVM GasConstants

/-- Total, pure dynamic gas schedule for Yul primitive operations bridged to `EvmYul.EVM.Gas`. -/
def yulPrimOpDynamicGas (fork : EVM.Fork) (s : Yul.State) (op : Operation .Yul) (args : List UInt256) : ℕ :=
  let a0 : UInt256 := args[0]?.getD ⟨0⟩
  let a1 : UInt256 := args[1]?.getD ⟨0⟩
  let a2 : UInt256 := args[2]?.getD ⟨0⟩
  let a3 : UInt256 := args[3]?.getD ⟨0⟩
  let shared := s.toSharedState
  let I := shared.executionEnv
  let A := shared.substate
  let σ := shared.accountMap
  match op with
  | .SLOAD =>
    let isWarm := A.accessedStorageKeys.contains (I.codeOwner, a0)
    CsloadPure fork isWarm
  | .SSTORE =>
    let v₀ : UInt256 :=
      match shared.σ₀.get? I.codeOwner with
      | none => ⟨0⟩
      | some acc => acc.storage.getD a0 ⟨0⟩
    let v : UInt256 :=
      match σ.get? I.codeOwner with
      | none => ⟨0⟩
      | some acc => acc.storage.getD a0 ⟨0⟩
    let isWarm := A.accessedStorageKeys.contains (I.codeOwner, a0)
    CsstorePure fork v₀ v a1 isWarm
  | .TLOAD => Ctload
  | .TSTORE => Ctstore
  | .KECCAK256 => Ckeccak256Pure a1
  | .EXP => CexpPure a1
  | .LOG0 => ClogPure 0 a1
  | .LOG1 => ClogPure 1 a1
  | .LOG2 => ClogPure 2 a1
  | .LOG3 => ClogPure 3 a1
  | .LOG4 => ClogPure 4 a1
  | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY | .MCOPY => CcopyPure a2
  | .EXTCODECOPY =>
    let isWarm := A.accessedAccounts.contains (AccountAddress.ofUInt256 a0)
    (if !fork.hasEIP2929 || isWarm then Gwarmaccess else Gcoldaccountaccess) + CcopyPure a3
  | .BALANCE | .EXTCODESIZE | .EXTCODEHASH =>
    let isWarm := A.accessedAccounts.contains (AccountAddress.ofUInt256 a0)
    if !fork.hasEIP2929 || isWarm then Gwarmaccess else Gcoldaccountaccess
  | .SELFDESTRUCT =>
    let r := AccountAddress.ofUInt256 a0
    let isWarm := A.accessedAccounts.contains r
    let targetDead := decide (EvmYul.State.dead σ r)
    let hasPositiveBalance : Bool := (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (·.balance)) != (⟨0⟩ : UInt256)
    CselfdestructPure fork isWarm targetDead hasPositiveBalance
  | .STOP | .RETURN | .REVERT => Gzero
  | .ADDRESS | .ORIGIN | .CALLER | .CALLVALUE | .CALLDATASIZE | .CODESIZE | .GASPRICE
  | .COINBASE | .TIMESTAMP | .NUMBER | .PREVRANDAO | .GASLIMIT | .CHAINID
  | .RETURNDATASIZE | .POP | .MSIZE | .GAS | .BASEFEE | .BLOBBASEFEE => Gbase
  | .ADD | .SUB | .NOT | .LT | .GT | .SLT | .SGT | .EQ | .ISZERO
  | .AND | .OR | .XOR | .BYTE | .SHL | .SHR | .SAR
  | .CALLDATALOAD | .MLOAD | .MSTORE | .MSTORE8 => Gverylow
  | .MUL | .DIV | .SDIV | .MOD | .SMOD | .SIGNEXTEND | .SELFBALANCE | .CLZ => Glow
  | .ADDMOD | .MULMOD => Gmid
  | .BLOCKHASH => Gblockhash
  | .BLOBHASH => HASH_OPCODE_GAS
  | _ => Gverylow

example (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .CLZ args = 5 := rfl

/-- Total memory expansion gas cost for Yul primitive operations using `memoryExpansionCostPure`. -/
def yulMemoryExpansionGas (s : Yul.State) (op : Operation .Yul) (args : List UInt256) : ℕ :=
  let aw := s.toMachineState.activeWords
  let a0 := (args[0]?.getD (⟨0⟩ : UInt256)).toNat
  let a1 := (args[1]?.getD (⟨0⟩ : UInt256)).toNat
  let a2 := (args[2]?.getD (⟨0⟩ : UInt256)).toNat
  let a3 := (args[3]?.getD (⟨0⟩ : UInt256)).toNat
  let a4 := (args[4]?.getD (⟨0⟩ : UInt256)).toNat
  let a5 := (args[5]?.getD (⟨0⟩ : UInt256)).toNat
  let a6 := (args[6]?.getD (⟨0⟩ : UInt256)).toNat
  let regions : List (ℕ × ℕ) :=
    match op with
    | .KECCAK256 | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 | .RETURN | .REVERT => [(a0, a1)]
    | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY => [(a0, a2)]
    | .MCOPY => [(max a0 a1, a2)]
    | .EXTCODECOPY | .CREATE | .CREATE2 => [(a1, a3)]
    | .MLOAD | .MSTORE => [(a0, 32)]
    | .MSTORE8 => [(a0, 1)]
    | .CALL | .CALLCODE => [(a3, a4), (a5, a6)]
    | .DELEGATECALL | .STATICCALL => [(a2, a3), (a4, a5)]
    | _ => []
  memoryExpansionCostPure aw regions

/-- Deduct `cost` gas from `s.toMachineState.gasAvailable`, throwing `.OutOfFuel` when
    `s.toMachineState.gasAvailable.toNat < cost`. -/
def consumeYulGas (s : Yul.State) (cost : ℕ) : Except Yul.Exception Yul.State :=
  let avail := s.toMachineState.gasAvailable.toNat
  if cost ≤ avail then
    let m' := { s.toMachineState with gasAvailable := UInt256.ofNat (avail - cost) }
    .ok (s.setMachineState m')
  else
    .error .OutOfFuel

/-- `consumeYulGas` returns `.error .OutOfFuel` if and only if `gasAvailable.toNat < cost`. -/
theorem consumeYulGas_outOfFuel_iff (s : Yul.State) (cost : ℕ) :
    consumeYulGas s cost = .error .OutOfFuel ↔ s.toMachineState.gasAvailable.toNat < cost := by
  unfold consumeYulGas
  dsimp
  split_ifs with h
  · simp [Nat.not_lt.mpr h]
  · simp [Nat.lt_of_not_ge h]

/-- Consuming 0 gas never throws `.OutOfFuel`. -/
theorem consumeYulGas_zero_ne_outOfFuel (s : Yul.State) :
    consumeYulGas s 0 ≠ .error .OutOfFuel := by
  intro h
  have hlt := (consumeYulGas_outOfFuel_iff s 0).mp h
  exact Nat.not_lt_zero _ hlt

/-- Base arithmetic Yul opcodes (`ADD`, `SUB`, `XOR`) always cost `Gverylow = 3` dynamic gas. -/
theorem yulPrimOpDynamicGas_add (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .ADD args = Gverylow := by
  rfl

/-- `SLOAD` dynamic gas in Yul is strictly positive across all forks and warm/cold states. -/
theorem yulPrimOpDynamicGas_sload_pos (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    0 < yulPrimOpDynamicGas fork s .SLOAD args := by
  unfold yulPrimOpDynamicGas
  exact csloadPure_pos fork _

/-- Non-memory opcodes (`ADD`) incur zero memory expansion gas in Yul when `activeWords` is canonical. -/
theorem memoryExpansionCostPure_nil (aw : UInt256) (h : UInt256.ofNat aw.toNat = aw) :
    memoryExpansionCostPure aw [] = 0 := by
  unfold memoryExpansionCostPure memoryExpansionWordsPure
  dsimp
  rw [h]
  exact Nat.sub_self _

end Yul

end EvmYul
