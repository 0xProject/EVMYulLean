import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.Account
import EvmYul.EVM.Gas

namespace EvmYul

namespace EVM

/-!
# Prague (Pectra) & Osaka (Fusaka) Formal Specifications

1. **EIP-7702**: EOA Code Delegation Designator (`0xef0100 || address`)
2. **EIP-2537 & EIP-7951**: BLS12-381 & P256VERIFY Precompile Gas Schedule
3. **EIP-2935**: Historical Block Hashes Ring Buffer (`HISTORY_SERVE_WINDOW = 8191`)
4. **EIP-6780**: Same-Transaction `SELFDESTRUCT` Semantics
-/

/-- EIP-7702 magic delegation prefix `0xef0100`. -/
def eip7702Prefix : List UInt8 := [0xef, 0x01, 0x00]

/-- Checks whether `code` is an EIP-7702 delegation designator (`0xef0100 || 20-byte address`). -/
def isDelegationDesignator (code : List UInt8) : Bool :=
  code.length == 23 && code.take 3 == eip7702Prefix

/-- Encodes a 20-byte address into an EIP-7702 delegation designator. -/
def encodeDelegationDesignator (addrBytes : List UInt8) : Option (List UInt8) :=
  if addrBytes.length == 20 then some (eip7702Prefix ++ addrBytes) else none

/-- Extracts the 20-byte delegated address from an EIP-7702 delegation designator. -/
def extractDelegatedBytes (code : List UInt8) : Option (List UInt8) :=
  if isDelegationDesignator code then some (code.drop 3) else none

/-- Roundtrip theorem for encoding and extracting an EIP-7702 delegation designator. -/
theorem extract_encode_delegation_roundtrip (addrBytes : List UInt8) (h : addrBytes.length = 20) :
    (encodeDelegationDesignator addrBytes >>= extractDelegatedBytes) = some addrBytes := by
  unfold encodeDelegationDesignator
  have hbeq : (addrBytes.length == 20) = true := beq_iff_eq.mpr h
  rw [hbeq, ite_eq_left rfl]
  change extractDelegatedBytes (eip7702Prefix ++ addrBytes) = some addrBytes
  unfold extractDelegatedBytes isDelegationDesignator eip7702Prefix
  have hlen : ([0xef, 0x01, 0x00] ++ addrBytes).length = 23 := by
    simp [h]
  have hlen_beq : (([0xef, 0x01, 0x00] ++ addrBytes).length == 23) = true :=
    beq_iff_eq.mpr hlen
  have htake : ([0xef, 0x01, 0x00] ++ addrBytes).take 3 = [0xef, 0x01, 0x00] := by
    rfl
  have htake_beq : (([0xef, 0x01, 0x00] ++ addrBytes).take 3 == [0xef, 0x01, 0x00]) = true :=
    beq_iff_eq.mpr htake
  rw [hlen_beq, htake_beq]
  rfl

/-- EIP-2537 `BLS12_G1ADD` precompile gas cost. -/
def bls12G1AddGas : ℕ := 375

/-- EIP-2537 `BLS12_G2ADD` precompile gas cost. -/
def bls12G2AddGas : ℕ := 600

/-- EIP-2537 `BLS12_MAP_FP_TO_G1` precompile gas cost. -/
def bls12MapFpToG1Gas : ℕ := 5500

/-- EIP-2537 `BLS12_MAP_FP2_TO_G2` precompile gas cost. -/
def bls12MapFp2ToG2Gas : ℕ := 23800

/-- EIP-2537 `BLS12_PAIRING_CHECK` gas cost for `k` pairs. -/
def bls12PairingGas (k : ℕ) : ℕ := 37700 + 32600 * k

/-- EIP-7951 `P256VERIFY` precompile gas cost. -/
def p256VerifyGas : ℕ := 6900

/-- `bls12PairingGas` is monotone in the number of pairing pairs `k`. -/
theorem bls12PairingGas_monotone {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    bls12PairingGas k₁ ≤ bls12PairingGas k₂ := by
  unfold bls12PairingGas
  omega

/-- `bls12PairingGas` is strictly positive for any number of pairs `k`. -/
theorem bls12PairingGas_pos (k : ℕ) : 0 < bls12PairingGas k := by
  unfold bls12PairingGas
  omega

/-- EIP-2935 historical block hashes ring buffer window (`HISTORY_SERVE_WINDOW = 8191`). -/
def historyServeWindow : ℕ := 8191

/-- EIP-2935 ring buffer storage slot for `blockNumber`. -/
def eip2935RingSlot (blockNumber : ℕ) : ℕ := blockNumber % historyServeWindow

/-- Every EIP-2935 ring buffer slot is strictly bounded by `historyServeWindow`. -/
theorem eip2935RingSlot_lt_window (n : ℕ) : eip2935RingSlot n < historyServeWindow := by
  unfold eip2935RingSlot historyServeWindow
  exact Nat.mod_lt n (by decide)

/-- EIP-6780 account deletion rule for `SELFDESTRUCT`. -/
def shouldDeleteAccountEIP6780 (fork : EVM.Fork) (wasCreatedInTx : Bool) : Bool :=
  match fork with
  | .Cancun | .Prague | .Osaka => wasCreatedInTx
  | _ => true

/-- Under EIP-6780 (`Cancun`, `Prague`, `Osaka`), pre-existing accounts (`wasCreatedInTx = false`)
    are preserved on `SELFDESTRUCT`. -/
theorem eip6780_preserves_preexisting_account (fork : EVM.Fork)
    (h : fork = .Cancun ∨ fork = .Prague ∨ fork = .Osaka) :
    shouldDeleteAccountEIP6780 fork false = false := by
  rcases h with rfl | rfl | rfl <;> rfl

end EVM

end EvmYul
