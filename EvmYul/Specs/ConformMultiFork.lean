import EvmYul.EVM.Gas
import EvmYul.EVM.PragueOsakaSpecs
import EvmYul.State.Transaction

namespace EvmYul

namespace EVM.Fork

/-- Parse supported EEST network names, including fork-prefixed variants. -/
def ofNetworkString (net : String) : Option EVM.Fork :=
  let cs := net.toList
  if "Shanghai".toList.isPrefixOf cs then some .Shanghai
  else if "Cancun".toList.isPrefixOf cs then some .Cancun
  else if "Prague".toList.isPrefixOf cs then some .Prague
  else if "Osaka".toList.isPrefixOf cs then some .Osaka
  else none

/-- Whether the conformance harness recognizes this network. -/
def isSupportedConformNetwork (net : String) : Bool :=
  (ofNetworkString net).isSome

theorem ofNetworkString_shanghai : ofNetworkString "Shanghai" = some .Shanghai := by
  decide

theorem ofNetworkString_cancun : ofNetworkString "Cancun" = some .Cancun := by
  decide

theorem ofNetworkString_prague : ofNetworkString "Prague" = some .Prague := by
  decide

theorem ofNetworkString_osaka : ofNetworkString "Osaka" = some .Osaka := by
  decide

/-- Unknown networks cannot silently select the default fork. -/
theorem ofNetworkString_unknown : ofNetworkString "London" = none := by
  decide

end EVM.Fork

namespace Conform

/-- Check the transaction's gas allowance using the selected fork. -/
def checkIntrinsicGasForFork (fork : EVM.Fork) (tx : Transaction) : Bool :=
  decide (EVM.intrinsicGas tx fork ≤ tx.base.gasLimit.toNat)

/-- EIP-3529 caps the refundable gas at one fifth of the gas used. -/
def effectiveGasRefund (gasUsed refundCounter : Nat) : Nat :=
  min refundCounter (gasUsed / 5)

/-- Net gas charged after applying the refund cap. -/
def netGasUsedAfterRefund (gasUsed refundCounter : Nat) : Nat :=
  gasUsed - effectiveGasRefund gasUsed refundCounter

theorem effectiveGasRefund_le_fifth (gasUsed refundCounter : Nat) :
    effectiveGasRefund gasUsed refundCounter ≤ gasUsed / 5 := by
  exact Nat.min_le_right _ _

/-- Exact integral lower bound; it is attained whenever the counter reaches the cap. -/
theorem netGasUsedAfterRefund_ge_four_fifths (gasUsed refundCounter : Nat) :
    gasUsed - gasUsed / 5 ≤ netGasUsedAfterRefund gasUsed refundCounter := by
  have h := effectiveGasRefund_le_fifth gasUsed refundCounter
  unfold netGasUsedAfterRefund
  omega

theorem netGasUsedAfterRefund_mul_five (gasUsed refundCounter : Nat) :
    4 * gasUsed ≤ 5 * netGasUsedAfterRefund gasUsed refundCounter := by
  have h := netGasUsedAfterRefund_ge_four_fifths gasUsed refundCounter
  omega

theorem effectiveGasRefund_at_cap (gasUsed : Nat) :
    effectiveGasRefund gasUsed (gasUsed / 5) = gasUsed / 5 := by
  simp [effectiveGasRefund]

theorem prague_intrinsicGas_ge_cancun (tx : Transaction) :
    EVM.intrinsicGas tx .Cancun ≤ EVM.intrinsicGas tx .Prague := by
  simp only [EVM.intrinsicGas, EVM.Fork.hasEIP7623, Bool.false_eq_true, ↓reduceIte]
  exact le_max_left _ _

end Conform
end EvmYul
