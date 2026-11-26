import EvmYul.Yul.MessageCallCombinator
import EvmYul.EVM.Gas
import EvmYul.Specs.GasSpec

namespace EvmYul

namespace Specs

open EvmYul.EVM EvmYul.Yul GasConstants

/-!
# EVM ↔ Yul Message Call & 63/64 Gas Forwarding Simulation (`E4-message-call-evm-yul-simulation`)

Connects `Yul.MessageCallCombinator` (`YulCallMode`, `YulCallParams`, `prepareChildCallEnv`,
`effectiveCodeOwner`, `effectiveSender`, `effectiveWeiValue`, `effectivePerm`) with the
Yellow Paper EIP-150 63/64ths gas forwarding function `EVM.L` and `GasConstants.Gcallstipend`,
providing machine-checked simulation invariants for `Verity 2.0` external call proofs.
-/

/-- Whether a message call mode carries a positive value transfer that triggers `Gcallstipend`.
    Only `.Call` and `.CallCode` with non-zero `params.value` receive the 2300 gas stipend;
    `.DelegateCall` and `.StaticCall` never add a stipend. -/
def callModeHasStipend (mode : YulCallMode) (callVal : UInt256) : Bool :=
  match mode with
  | .Call | .CallCode => callVal != ⟨0⟩
  | .DelegateCall | .StaticCall => false

/-- 63/64ths message-call gas forwarded to the child frame (Yellow Paper Eq. 326 `Ccallgas`):
    `min requestedGas (L (availGas - cextra)) + (if hasPositiveValue then Gcallstipend else 0)`. -/
def forwardedCallGas (availGas cextra requestedGas : Nat) (hasPositiveValue : Bool) : Nat :=
  min requestedGas (EVM.L (availGas - cextra)) +
    (if hasPositiveValue then GasConstants.Gcallstipend else 0)

/-- Caller's remaining gas after a child call returns `childGasRemaining` unspent gas,
    given initial `availGas` and total charged call gas `totalCallCost` (`cextra + capGas`). -/
def callerGasAfterChildReturn (availGas totalCallCost childGasRemaining : Nat) : Nat :=
  (availGas - totalCallCost) + childGasRemaining

/-- Theorem 1: When `hasPositiveValue = false` (no value transfer, or `STATICCALL` / `DELEGATECALL`),
    the gas forwarded to the child call is bounded above by both `requestedGas` and `L (availGas - cextra)`. -/
theorem forwardedCallGas_no_stipend_le_L (availGas cextra requestedGas : Nat) :
    forwardedCallGas availGas cextra requestedGas false ≤ requestedGas ∧
    forwardedCallGas availGas cextra requestedGas false ≤ EVM.L (availGas - cextra) := by
  unfold forwardedCallGas
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

/-- Theorem 2: Under `STATICCALL` or `DELEGATECALL`, `callModeHasStipend` is unconditionally `false`,
    so `forwardedCallGas` never adds `Gcallstipend` (`2300`) and strictly obeys the `L (availGas - cextra)` cap. -/
theorem forwardedCallGas_static_and_delegate_no_stipend
    (availGas cextra requestedGas : Nat) (callVal : UInt256) :
    forwardedCallGas availGas cextra requestedGas (callModeHasStipend .StaticCall callVal) =
      min requestedGas (EVM.L (availGas - cextra)) ∧
    forwardedCallGas availGas cextra requestedGas (callModeHasStipend .DelegateCall callVal) =
      min requestedGas (EVM.L (availGas - cextra)) := by
  exact ⟨rfl, rfl⟩

/-- Theorem 3: When `hasPositiveValue = false` and `64 ≤ availGas - cextra`, the gas forwarded
    to the child call is strictly less than the caller's post-extra gas `availGas - cextra`
    (guaranteed positive gas retention in the caller frame). -/
theorem forwardedCallGas_no_stipend_strict_lt_avail
    {availGas cextra : Nat} (requestedGas : Nat)
    (hGe64 : 64 ≤ availGas - cextra) :
    forwardedCallGas availGas cextra requestedGas false < availGas - cextra := by
  have ⟨_, hLeL⟩ := forwardedCallGas_no_stipend_le_L availGas cextra requestedGas
  have hLt := L_lt_self_of_ge_64 hGe64
  omega

/-- Theorem 4: `prepareChildCallEnv` increments call depth by exactly `1` and installs `calldata`
    across all four message-call modes (`CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`). -/
theorem prepareChildCallEnv_depth_and_calldata
    (mode : YulCallMode) (parentEnv : ExecutionEnv .Yul)
    (params : YulCallParams) (cd : ByteArray) :
    (prepareChildCallEnv mode parentEnv params cd).depth = parentEnv.depth + 1 ∧
    (prepareChildCallEnv mode parentEnv params cd).calldata = cd := by
  exact ⟨rfl, rfl⟩

/-- Theorem 5: Standard `.Call` sets child `codeOwner = params.target`, `source = parentEnv.codeOwner`
    (`CALLER`), preserves `sender = parentEnv.sender` (`ORIGIN`), sets `weiValue = params.value`,
    and inherits `perm = parentEnv.perm`. -/
theorem prepareChildCallEnv_call_owner_and_sender
    (parentEnv : ExecutionEnv .Yul) (params : YulCallParams) (cd : ByteArray) :
    let child := prepareChildCallEnv .Call parentEnv params cd
    child.codeOwner = params.target ∧
    child.source = parentEnv.codeOwner ∧
    child.sender = parentEnv.sender ∧
    child.weiValue = params.value ∧
    child.perm = parentEnv.perm := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 6: `.StaticCall` sets child `codeOwner = params.target`, `source = parentEnv.codeOwner`
    (`CALLER`), preserves `sender = parentEnv.sender` (`ORIGIN`), forces `weiValue = 0`, and
    enforces `perm = false` regardless of `parentEnv.perm`. -/
theorem prepareChildCallEnv_staticCall_invariants
    (parentEnv : ExecutionEnv .Yul) (params : YulCallParams) (cd : ByteArray) :
    let child := prepareChildCallEnv .StaticCall parentEnv params cd
    child.codeOwner = params.target ∧
    child.source = parentEnv.codeOwner ∧
    child.sender = parentEnv.sender ∧
    child.weiValue = ⟨0⟩ ∧
    child.perm = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 7: Whenever `totalCallCost ≤ availGas` and the child returns `childGasRemaining ≤ totalCallCost`,
    the caller's post-return gas `callerGasAfterChildReturn availGas totalCallCost childGasRemaining`
    never exceeds `availGas`, and equals `availGas - (totalCallCost - childGasRemaining)`. -/
theorem callerGasAfterChildReturn_le_avail
    {availGas totalCallCost childGasRemaining : Nat}
    (hCost : totalCallCost ≤ availGas)
    (hRem : childGasRemaining ≤ totalCallCost) :
    callerGasAfterChildReturn availGas totalCallCost childGasRemaining =
      availGas - (totalCallCost - childGasRemaining) ∧
    callerGasAfterChildReturn availGas totalCallCost childGasRemaining ≤ availGas := by
  unfold callerGasAfterChildReturn
  omega

end Specs

end EvmYul
