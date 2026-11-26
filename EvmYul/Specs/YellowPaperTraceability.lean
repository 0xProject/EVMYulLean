import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace Specs

open EvmYul.EVM GasConstants

/-- EIP-3860 maximum initcode size in bytes (`2 * MAX_CODE_SIZE = 49152`). -/
def maxInitcodeSize : ℕ := 49152

/-- EIP-7623 calldata token count: `zeroBytes + 4 * nonZeroBytes`. -/
def eip7623TokensInCalldata (zeroBytes nonZeroBytes : ℕ) : ℕ :=
  zeroBytes + 4 * nonZeroBytes

/-- EIP-7623 Prague/Osaka calldata floor gas: `Gtransaction + 10 * tokens`. -/
def eip7623FloorGas (zeroBytes nonZeroBytes : ℕ) : ℕ :=
  Gtransaction + 10 * eip7623TokensInCalldata zeroBytes nonZeroBytes

/-- Pre-Prague intrinsic calldata + base tx gas (no access list, non-create). -/
def standardCalldataTxGas (zeroBytes nonZeroBytes : ℕ) : ℕ :=
  Gtransaction + Gtxdatazero * zeroBytes + Gtxdatanonzero * nonZeroBytes

/-- Prague/Osaka intrinsic calldata + base tx gas with EIP-7623 floor. -/
def pragueCalldataTxGas (zeroBytes nonZeroBytes : ℕ) : ℕ :=
  max (standardCalldataTxGas zeroBytes nonZeroBytes) (eip7623FloorGas zeroBytes nonZeroBytes)

/-- Yellow Paper equation traceability registry linking equation numbers to `EVMYulLean 2.0` symbols. -/
structure YellowPaperEquation where
  equationNumber : ℕ
  sectionRef : String
  leanSymbol : String
  deriving DecidableEq, Repr, BEq, Inhabited

def yellowPaperEquationRegistry : List YellowPaperEquation :=
  [ { equationNumber := 43,  sectionRef := "9.4.3",      leanSymbol := "EvmYul.EVM.D_J_total" }
  , { equationNumber := 65,  sectionRef := "6.2",        leanSymbol := "EvmYul.EVM.R" }
  , { equationNumber := 326, sectionRef := "Appendix H", leanSymbol := "EvmYul.MachineState.M" }
  , { equationNumber := 328, sectionRef := "Appendix H", leanSymbol := "EvmYul.EVM.Cₘ" }
  , { equationNumber := 331, sectionRef := "Appendix H", leanSymbol := "EvmYul.EVM.L" }
  ]

/-- Yellow Paper Eq. (328): Memory gas cost of 0 active words is 0. -/
theorem yp_eq_328_memory_zero : Cₘ ⟨0⟩ = 0 := by
  decide

/-- Yellow Paper Eq. (328): Memory gas cost of 1 active word is `Gmemory = 3`. -/
theorem yp_eq_328_memory_one : Cₘ (.ofNat 1) = 3 := by
  decide

/-- Yellow Paper Eq. (328): Memory gas cost is monotonically non-decreasing in word count. -/
theorem yp_eq_328_memory_monotone {a b : UInt256} (h : a.toNat ≤ b.toNat) :
    Cₘ a ≤ Cₘ b := by
  unfold Cₘ Cₘ.QuadraticCeofficient
  dsimp
  have hmul : Gmemory * a.toNat ≤ Gmemory * b.toNat := Nat.mul_le_mul_left Gmemory h
  have hsq : a.toNat * a.toNat ≤ b.toNat * b.toNat := Nat.mul_le_mul h h
  have hdiv : (a.toNat * a.toNat) / 512 ≤ (b.toNat * b.toNat) / 512 :=
    Nat.div_le_div_right hsq
  omega

/-- Yellow Paper Eq. (331): The EIP-150 message-call gas cap `L(n) = n - n / 64` never exceeds `n`. -/
theorem yp_eq_331_cap_le_self (n : ℕ) : L n ≤ n := by
  unfold L
  omega

/-- Yellow Paper Eq. (331): For `n < 64`, the 1/64th deduction rounds down to 0 so `L(n) = n`. -/
theorem yp_eq_331_cap_eq_self_of_lt_64 {n : ℕ} (h : n < 64) : L n = n := by
  unfold L
  omega

/-- Yellow Paper Eq. (331): For `64 ≤ n`, the EIP-150 cap is strictly less than `n`. -/
theorem yp_eq_331_cap_strict_lt {n : ℕ} (h : 64 ≤ n) : L n < n := by
  unfold L
  omega

/-- Yellow Paper Eq. (65) / EIP-3860: Initcode word gas `R(x)` for `x ≤ 49152` is bounded by `3072`. -/
theorem yp_eq_65_initcode_word_bound {x : ℕ} (h : x ≤ maxInitcodeSize) :
    R x ≤ 3072 := by
  unfold R Ginitcodeword maxInitcodeSize at *
  omega

/-- Yellow Paper Eq. (65) / EIP-3860: The `3072` gas bound is tight at `x = maxInitcodeSize = 49152`. -/
theorem yp_eq_65_initcode_word_bound_tight :
    R maxInitcodeSize = 3072 := by
  decide

/-- EIP-7623 (Prague/Osaka): Prague calldata tx gas is always at least the pre-Prague standard gas. -/
theorem eip7623_prague_ge_cancun (zeroBytes nonZeroBytes : ℕ) :
    standardCalldataTxGas zeroBytes nonZeroBytes ≤ pragueCalldataTxGas zeroBytes nonZeroBytes := by
  unfold pragueCalldataTxGas
  exact Nat.le_max_left _ _

/-- EIP-7623 (Prague/Osaka): For zero-byte calldata (`nonZeroBytes = 0`, `0 < zeroBytes`),
    the EIP-7623 floor (`10` gas/byte) strictly dominates standard calldata gas (`4` gas/byte). -/
theorem eip7623_prague_floor_dominates_zero_heavy {zeroBytes : ℕ} (h : 0 < zeroBytes) :
    standardCalldataTxGas zeroBytes 0 < pragueCalldataTxGas zeroBytes 0 := by
  unfold pragueCalldataTxGas standardCalldataTxGas eip7623FloorGas eip7623TokensInCalldata
  unfold Gtransaction Gtxdatazero Gtxdatanonzero
  omega

/-- Full transaction-level `intrinsicGas` monotonicity from `Cancun` to `Prague`. -/
theorem intrinsicGas_cancun_le_prague (T : Transaction) :
    intrinsicGas T .Cancun ≤ intrinsicGas T .Prague := by
  unfold intrinsicGas Fork.hasEIP7623
  simp

end Specs

end EvmYul
