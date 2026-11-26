import EvmYul.UInt256
import Std.Tactic.BVDecide

namespace EvmYul.UInt256

open BitVec

theorem add_comm (a b : UInt256) : a + b = b + a := by
  apply UInt256.ext
  simp only [add_toBitVec]
  exact BitVec.add_comm a.toBitVec b.toBitVec

theorem add_assoc (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply UInt256.ext
  simp only [add_toBitVec]
  exact BitVec.add_assoc a.toBitVec b.toBitVec c.toBitVec

theorem add_zero (a : UInt256) : a + ⟨0⟩ = a := by
  apply UInt256.ext
  simp only [add_toBitVec]
  bv_decide

theorem zero_add (a : UInt256) : ⟨0⟩ + a = a := by
  apply UInt256.ext
  simp only [add_toBitVec]
  bv_decide

theorem sub_self (a : UInt256) : a - a = ⟨0⟩ := by
  apply UInt256.ext
  simp only [sub_toBitVec]
  bv_decide

theorem add_sub_cancel (a b : UInt256) : (a + b) - b = a := by
  apply UInt256.ext
  simp only [add_toBitVec, sub_toBitVec]
  bv_decide

theorem sub_add_cancel (a b : UInt256) : (a - b) + b = a := by
  apply UInt256.ext
  simp only [add_toBitVec, sub_toBitVec]
  bv_decide

theorem mul_comm (a b : UInt256) : a * b = b * a := by
  apply UInt256.ext
  simp only [mul_toBitVec]
  exact BitVec.mul_comm a.toBitVec b.toBitVec

theorem mul_one (a : UInt256) : a * ⟨1⟩ = a := by
  apply UInt256.ext
  simp [mul_toBitVec]

theorem one_mul (a : UInt256) : ⟨1⟩ * a = a := by
  apply UInt256.ext
  simp [mul_toBitVec]

theorem mul_zero (a : UInt256) : a * ⟨0⟩ = ⟨0⟩ := by
  apply UInt256.ext
  simp [mul_toBitVec]

theorem zero_mul (a : UInt256) : ⟨0⟩ * a = ⟨0⟩ := by
  apply UInt256.ext
  simp [mul_toBitVec]

theorem toNat_lt_size (a : UInt256) : a.toNat < UInt256.size := by
  simpa [UInt256.toNat, UInt256.size] using a.toBitVec.isLt

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  cases a with
  | mk bv =>
    apply UInt256.ext
    change BitVec.ofNat 256 bv.toNat = bv
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem toNat_ofNat (n : Nat) : (UInt256.ofNat n).toNat = n % UInt256.size := by
  simp [UInt256.ofNat, UInt256.toNat, UInt256.size, BitVec.toNat_ofNat]

theorem eq0_zero : UInt256.eq0 ⟨0⟩ = true := by
  rfl

theorem eq0_one : UInt256.eq0 ⟨1⟩ = false := by
  rfl

end EvmYul.UInt256
