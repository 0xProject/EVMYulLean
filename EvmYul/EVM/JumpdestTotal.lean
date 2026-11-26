import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

namespace EVM

def nextPcAfterOp (opByte : UInt8) (pc : Nat) : Nat :=
  if 0x60 ≤ opByte ∧ opByte ≤ 0x7f then pc + (opByte.toNat - 0x60 + 1) + 1 else pc + 1

theorem nextPcAfterOp_gt (opByte : UInt8) (pc : Nat) : pc < nextPcAfterOp opByte pc := by
  unfold nextPcAfterOp
  split <;> omega

def collectJumpdestsAux (c : ByteArray) (pc : Nat) (fuel : Nat) (acc : Array UInt256) : Array UInt256 :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    match c.get? pc with
    | none => acc
    | some opByte =>
      let acc' := if opByte == 0x5b then acc.push (UInt256.ofNat pc) else acc
      collectJumpdestsAux c (nextPcAfterOp opByte pc) fuel' acc'

def collectJumpdests (c : ByteArray) : Array UInt256 :=
  collectJumpdestsAux c 0 c.size #[]

def D_J_total (c : ByteArray) : Array UInt256 :=
  collectJumpdests c

theorem collectJumpdestsAux_zero (c : ByteArray) (pc : Nat) (acc : Array UInt256) :
    collectJumpdestsAux c pc 0 acc = acc := rfl

theorem nextPcAfterOp_push1 (pc : Nat) :
    nextPcAfterOp 0x60 pc = pc + 2 := rfl

theorem nextPcAfterOp_non_push (opByte : UInt8) (pc : Nat) (h : ¬(0x60 ≤ opByte ∧ opByte ≤ 0x7f)) :
    nextPcAfterOp opByte pc = pc + 1 := by
  unfold nextPcAfterOp
  exact ite_eq_right h

theorem collectJumpdests_size_ge_acc (c : ByteArray) (pc : Nat) (fuel : Nat) (acc : Array UInt256) :
    acc.size ≤ (collectJumpdestsAux c pc fuel acc).size := by
  induction fuel generalizing pc acc with
  | zero =>
    exact Nat.le_refl acc.size
  | succ fuel' ih =>
    unfold collectJumpdestsAux
    cases c.get? pc with
    | none =>
      exact Nat.le_refl acc.size
    | some opByte =>
      dsimp only
      split
      · have hpush : acc.size ≤ (acc.push (UInt256.ofNat pc)).size := by
          simp
        exact Nat.le_trans hpush (ih (nextPcAfterOp opByte pc) (acc.push (UInt256.ofNat pc)))
      · exact ih (nextPcAfterOp opByte pc) acc

end EVM

end EvmYul
