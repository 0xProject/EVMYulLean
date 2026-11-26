import Init.Data.Nat.Div
import Std.Tactic.BVDecide
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace EvmYul

/-- The size of type `UInt256`, that is, `2^256`. -/
@[reducible]
def UInt256.size : ℕ := 2 ^ 256

instance : NeZero UInt256.size where
  out := by decide

/-- 256-bit EVM/Yul word backed directly by Lean 4 `BitVec 256`. -/
structure UInt256 where
  toBitVec : BitVec 256
  deriving BEq, DecidableEq, Hashable

namespace UInt256

/-- Zero-cost projection to `Fin UInt256.size` (`BitVec.toFin`), preserving 100% compatibility
    with existing `Fin`-based proofs while exposing `toBitVec : BitVec 256` for `bv_decide`. -/
@[inline, reducible]
def val (a : UInt256) : Fin UInt256.size := a.toBitVec.toFin

@[inline, reducible]
def ofBitVec (bv : BitVec 256) : UInt256 := ⟨bv⟩

instance : Coe (Fin UInt256.size) (BitVec 256) := ⟨BitVec.ofFin⟩

theorem ext {a b : UInt256} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; congr

theorem ext_val {a b : UInt256} (h : a.val = b.val) : a = b := by
  cases a with | mk a =>
  cases b with | mk b =>
  cases a; cases b
  simp only [val] at h
  congr

@[simp]
theorem toBitVec_ofBitVec (bv : BitVec 256) : (ofBitVec bv).toBitVec = bv := rfl

@[simp]
theorem ofBitVec_toBitVec (a : UInt256) : ofBitVec a.toBitVec = a := rfl

instance : ToString UInt256 where
  toString a := toString a.val

def ofNat (n : ℕ) : UInt256 :=
  ⟨BitVec.ofNat 256 n⟩

def toNat (u : UInt256) : ℕ := u.toBitVec.toNat

@[simp]
theorem val_mk (bv : BitVec 256) : (UInt256.mk bv).val = bv.toFin := rfl

@[simp]
theorem toNat_mk (bv : BitVec 256) : (UInt256.mk bv).toNat = bv.toNat := rfl

theorem toNat_eq_val (u : UInt256) : u.toNat = u.val.val := rfl

theorem toBitVec_toNat (u : UInt256) : u.toBitVec.toNat = u.toNat := rfl

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

instance : LawfulBEq UInt256 where
  eq_of_beq {a b} h := by
    cases a with | mk a =>
    cases b with | mk b =>
    exact congrArg UInt256.mk (LawfulBEq.eq_of_beq (α := BitVec 256) (a := a) (b := b) h)
  rfl {a} := by
    cases a with | mk a =>
    exact ReflBEq.rfl (α := BitVec 256) (a := a)

/-- Order `UInt256` by the underlying bitvector's natural value.
This is definitionally `compare` on `Nat`, so the tree-map laws apply. -/
@[reducible]
def uint256Cmp (a b : UInt256) : Ordering := compare a.toBitVec.toNat b.toBitVec.toNat

@[reducible]
instance : Ord UInt256 where
  compare := uint256Cmp

instance : Std.TransCmp uint256Cmp where
  eq_swap {a b} := by
    unfold uint256Cmp
    exact Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))
      (a := a.toBitVec.toNat) (b := b.toBitVec.toNat)
  isLE_trans {a b c} h₁ h₂ := by
    unfold uint256Cmp at *
    exact Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering))
      (a := a.toBitVec.toNat) (b := b.toBitVec.toNat) (c := c.toBitVec.toNat) h₁ h₂

instance : Std.LawfulEqCmp uint256Cmp where
  eq_of_compare {a b} h := by
    unfold uint256Cmp at h
    have hnat := Std.LawfulEqCmp.eq_of_compare
      (cmp := (compare : Nat → Nat → Ordering))
      (a := a.toBitVec.toNat) (b := b.toBitVec.toNat) h
    apply UInt256.ext
    exact BitVec.eq_of_toNat_eq hnat
  compare_self {a} := by
    unfold uint256Cmp
    exact Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering)) (a := a.toBitVec.toNat)

instance : Std.LawfulBEqCmp uint256Cmp where
  compare_eq_iff_beq {a b} := by
    unfold uint256Cmp
    constructor
    · intro h
      have hnat := Std.LawfulEqCmp.eq_of_compare
        (cmp := (compare : Nat → Nat → Ordering))
        (a := a.toBitVec.toNat) (b := b.toBitVec.toNat) h
      have hab : a = b := UInt256.ext (BitVec.eq_of_toNat_eq hnat)
      subst hab
      exact ReflBEq.rfl (α := UInt256) (a := a)
    · intro h
      have hab : a = b := LawfulBEq.eq_of_beq h
      subst hab
      exact Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering)) (a := a.toBitVec.toNat)

instance {n : ℕ} : OfNat (Fin UInt256.size) n := ⟨Fin.ofNat _ n⟩
instance {n : ℕ} : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩

end UInt256

export UInt256 (uint256Cmp)

end EvmYul

section CastUtils

open EvmYul UInt256

abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 :=
  ⟨BitVec.ofFin ⟨a.toNat, Nat.lt_trans a.toFin.2 (by decide)⟩⟩
def Bool.toUInt256 (b : Bool) : UInt256 :=
  if b then UInt256.ofNat 1 else UInt256.ofNat 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = UInt256.ofNat 1 := rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = UInt256.ofNat 0 := rfl

end CastUtils

namespace EvmYul

namespace UInt256

def add (a b : UInt256) : UInt256 := ⟨a.toBitVec + b.toBitVec⟩
def sub (a b : UInt256) : UInt256 := ⟨a.toBitVec - b.toBitVec⟩
def mul (a b : UInt256) : UInt256 := ⟨a.toBitVec * b.toBitVec⟩
def div (a b : UInt256) : UInt256 := ⟨a.toBitVec / b.toBitVec⟩
def mod (a b : UInt256) : UInt256 := if b.val == 0 then ⟨0⟩ else ⟨a.toBitVec % b.toBitVec⟩
def modn (a : UInt256) (n : ℕ) : UInt256 := ⟨BitVec.ofFin (Fin.modn a.val n)⟩
def land (a b : UInt256) : UInt256  := ⟨BitVec.ofFin (Fin.land a.val b.val)⟩
def lor (a b : UInt256) : UInt256   := ⟨BitVec.ofFin (Fin.lor a.val b.val)⟩
def xor (a b : UInt256) : UInt256   := ⟨BitVec.ofFin (Fin.xor a.val b.val)⟩
def shiftLeft (a b : UInt256) : UInt256  :=
  if b.val >= 256 then ⟨0⟩ else ⟨BitVec.ofFin (a.val <<< b.val)⟩
def shiftRight (a b : UInt256) : UInt256 :=
  if b.val >= 256 then ⟨0⟩ else ⟨BitVec.ofFin (a.val >>> b.val)⟩
def log2 (a : UInt256) : UInt256 := ⟨BitVec.ofFin (Fin.log2 a.val)⟩

/-- Counts leading zero bits in a 256-bit word (EIP-7939); returns `256` for `0`. -/
def clz (a : UInt256) : UInt256 :=
  if a.toNat = 0 then ofNat 256 else ofNat (255 - Nat.log2 a.toNat)

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩

@[simp] theorem add_toBitVec (a b : UInt256) : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
@[simp] theorem sub_toBitVec (a b : UInt256) : (a - b).toBitVec = a.toBitVec - b.toBitVec := rfl
@[simp] theorem mul_toBitVec (a b : UInt256) : (a * b).toBitVec = a.toBitVec * b.toBitVec := rfl
@[simp] theorem div_toBitVec (a b : UInt256) : (a / b).toBitVec = a.toBitVec / b.toBitVec := rfl

instance : LT UInt256 where
  lt a b := LT.lt a.val b.val

instance : LE UInt256 where
  le a b := LE.le a.val b.val

instance : Preorder UInt256 where
  le_refl := by intro; apply Nat.le_refl
  le_trans := by intro _ _ _ h₁ h₂ ; apply Nat.le_trans h₁ h₂
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_ge := by intros; rfl

def complement (a : UInt256) : UInt256 := ⟨BitVec.ofFin (0 - (a.val + 1))⟩

def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1) - a

def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then ⟨BitVec.ofFin (a.val * (-1))⟩
  else a

def fromSigned (a : UInt256) : ℤ :=
  if a.toNat < 2^255 then a.val else - (Nat.xor (UInt256.size - 1) a.val) - 1

def toSigned (i : ℤ) : UInt256 :=
  match i with
    | .ofNat n => ofNat n
    | .negSucc n => ofNat (UInt256.size - 1 - n)

instance : Complement UInt256 := ⟨EvmYul.UInt256.complement⟩

/-- Binary exponentiation accumulator. Made public for downstream verification. -/
def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(_ + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux ⟨1⟩ b n.val

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

def decLt (a b : UInt256) : Decidable (a < b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n < m))

def decLe (a b : UInt256) : Decidable (a ≤ b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt256) : Decidable (a < b) := decLt _ _
instance (a b : UInt256) : Decidable (a ≤ b) := UInt256.decLe a b
instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

/-- Zero test via propositional equality so `simp` discharges `a ≠ ⟨0⟩` goals directly. -/
def eq0 (a : UInt256) : Bool := decide (a = ⟨0⟩)

def byteAt (a b : UInt256) : UInt256 :=
  if a > ⟨31⟩ then ⟨0⟩ else
    b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& ⟨0xFF⟩

def sgn (a : UInt256) : ℤ :=
  if 2 ^ 255 <= a.toNat then
    -1
  else
    if eq0 a then 0 else 1

def bigUInt : UInt256 := ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else ⟨BitVec.ofFin ((abs a / b).val * -1)⟩
  else
    if 2 ^ 255 <= b.toNat then
      ⟨BitVec.ofFin ((a / abs b).val * -1)⟩
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then ⟨0⟩
  else
    toSigned <| sgn a * (abs a % abs b).toNat

def sltBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b.toNat ≥ 2 ^ 255 then false
    else a < b

def sgtBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b.toNat ≥ 2 ^ 255 then true
    else a > b

abbrev fromBool := Bool.toUInt256

def slt (a b : UInt256) :=
  fromBool (sltBool a b)

def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

def sar (a b : UInt256) : UInt256 :=
  if sltBool b ⟨0⟩
  then UInt256.complement (UInt256.complement b >>> a)
  else b >>> a

def signextend (a b : UInt256) : UInt256 :=
  if a.toNat ≤ 31 then
    let test_bit := a * ⟨8⟩ + ⟨7⟩
    let sign_bit := ⟨1⟩ <<< test_bit
    if b &&& sign_bit ≠ ⟨0⟩ then
      b ||| (UInt256.size.toUInt256 - sign_bit)
    else b &&& (sign_bit - ⟨1⟩)
  else b

def addMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val + b.val) c.toNat

def mulMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val * b.val) c.toNat

def exp (a b : UInt256) : UInt256 := pow a b

def lt (a b : UInt256) := fromBool (a < b)

def gt (a b : UInt256) := fromBool (a > b)

def eq (a b : UInt256) := fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end UInt256

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.toFin.val + 2^8 * fromBytes' bs

def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse
def fromByteArrayBigEndian (b : ByteArray) : ℕ := fromBytesBigEndian b.data.toList

variable {bs : List UInt8}
         {n : ℕ}

-- | A bound for the natural number value of a list of bytes.
private lemma fromBytes'_le : fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold fromBytes'; simp
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

-- | The natural number value of a length 32 list of bytes is < 2^256.
lemma fromBytes'_UInt256_le (h : bs.length = 32) : fromBytes' bs < 2^256 := by
    have h' := @fromBytes'_le bs
    rw [h] at h'
    exact h'

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := ⟨Nat.mod n UInt8.size, Nat.mod_lt _ (by linarith)⟩
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

@[simp]
lemma toBytesBigEndian_128 : toBytesBigEndian 128 = [UInt8.ofNat 128] := by
  simp [toBytesBigEndian, toBytes', UInt8.size]
  decide

-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
private lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [toBytes']
    | .succ n =>
      unfold toBytes'
      simp
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
lemma toBytes'_UInt256_le (h : n < UInt256.size) : (toBytes' n).length ≤ 32 := toBytes'_le h

/-- The big-endian byte expansion of a value below `UInt256.size` fits in 32 bytes.

`toBytes'` is private to this module, so downstream files cannot derive this from
`toBytes'_UInt256_le` themselves; it is exported here because `UInt256.toByteArray`
zero-pads against exactly this bound. -/
theorem length_toBytesBigEndian_le (h : n < UInt256.size) :
    (toBytesBigEndian n).length ≤ 32 := by
  simpa [toBytesBigEndian] using toBytes'_UInt256_le h

lemma toBytesBigEndian_UInt256_len_le (val : UInt256) :
    (toBytesBigEndian val.toNat).length ≤ 32 :=
  length_toBytesBigEndian_le val.val.isLt

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

-- | The length of a `zeroPadBytes` call is its first argument.
lemma zeroPadBytes_len (h : bs.length ≤ n) : (zeroPadBytes n bs).length = n := by
  unfold zeroPadBytes
  aesop

-- | Appending a bunch of zeroes to a little-endian list of bytes doesn't change its value.
@[simp]
private lemma extend_bytes_zero : fromBytes' (bs ++ List.replicate n 0) = fromBytes' bs := by
  induction bs with
  | nil =>
    simp [fromBytes']
    induction n with
    | zero => simp [List.replicate, fromBytes']
    | succ _ ih => simp [List.replicate, fromBytes']; norm_cast
  | cons _ _ ih => simp [fromBytes', ih]

-- | The ℕ value of a little-endian list of bytes is invariant under right zero-padding up to length 32.
@[simp]
lemma fromBytes'_zeroPadBytes_32_eq : fromBytes' (zeroPadBytes 32 bs) = fromBytes' bs := extend_bytes_zero

-- | Casting a natural number to a list of bytes and back is the identity.
@[simp]
lemma fromBytes'_toBytes' {x : ℕ} : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp
    have := Nat.div_lt_self (Nat.zero_lt_succ n) (by decide : 1 < UInt8.size)
    rw [fromBytes'_toBytes']
    simp [UInt8.size, add_comm]
    apply Nat.div_add_mod

@[simp]
lemma fromBytesBigEndian_toBytesBigEndian (x : ℕ) :
    fromBytesBigEndian (toBytesBigEndian x) = x := by
  unfold fromBytesBigEndian toBytesBigEndian
  simp [fromBytes'_toBytes']

@[simp]
lemma fromBytesBigEndian_zeroes_append (n : ℕ) (bs : List UInt8) :
    fromBytesBigEndian (List.replicate n 0 ++ bs) = fromBytesBigEndian bs := by
  unfold fromBytesBigEndian
  change fromBytes' ((List.replicate n 0 ++ bs).reverse) = fromBytes' bs.reverse
  rw [List.reverse_append]
  simp [extend_bytes_zero]

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

private lemma fromBytes_was_good_all_year_long
  (h : bs.length ≤ 32) : fromBytes' bs < 2^256 := by
  have h' := @fromBytes'_le bs
  rw [pow_mul] at h'
  refine lt_of_lt_of_le (b := (2 ^ 8) ^ List.length bs) h' ?lenBs
  case lenBs => rw [←pow_mul]; exact pow_le_pow_right₀ (by decide) (by linarith)

@[simp]
lemma fromBytes_wasnt_naughty : fromBytes! bs < 2^256 := fromBytes_was_good_all_year_long (by simp)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  ⟨BitVec.ofFin ⟨fromBytes! bs, fromBytes_wasnt_naughty⟩⟩

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.toNat)

/-! ## Byte *contents* of the big-endian encoding

`toBytes'` is private, well-founded, and variable-length, so downstream files can
say how *long* an encoding is but not what is *in* it. The definitions below are
the public, fixed-width, structurally recursive counterparts, and
`toBeBytesFixed_eq_zeroPad` is the bridge that identifies them with
`toBytesBigEndian` under left zero-padding. Everything a consumer needs about
individual bytes then follows from `getElem_toLeBytesFixed` without ever
mentioning `toBytes'`. -/

/-- The width-`w` little-endian base-256 expansion of `n`. Structural in the
width, hence unfoldable by consumers, unlike `toBytes'`. -/
def toLeBytesFixed : ℕ → ℕ → List UInt8
  | _, 0 => []
  | n, w + 1 => UInt8.ofNat (n % 256) :: toLeBytesFixed (n / 256) w

/-- The width-`w` big-endian base-256 expansion of `n`. -/
def toBeBytesFixed (n w : ℕ) : List UInt8 := (toLeBytesFixed n w).reverse

@[simp] lemma length_toLeBytesFixed (n w : ℕ) : (toLeBytesFixed n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toLeBytesFixed, ih]

@[simp] lemma length_toBeBytesFixed (n w : ℕ) : (toBeBytesFixed n w).length = w := by
  simp [toBeBytesFixed]

/-- **Every digit of the little-endian expansion, in closed form.** -/
lemma getElem_toLeBytesFixed (n w i : ℕ) (h : i < (toLeBytesFixed n w).length) :
    (toLeBytesFixed n w)[i] = UInt8.ofNat (n / 256 ^ i % 256) := by
  induction w generalizing n i with
  | zero => simp at h
  | succ w ih =>
    match i with
    | 0 => simp [toLeBytesFixed]
    | i + 1 =>
      have h' : i < (toLeBytesFixed (n / 256) w).length := by
        simp only [length_toLeBytesFixed] at h ⊢; omega
      have : n / 256 / 256 ^ i = n / 256 ^ (i + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simpa [toLeBytesFixed, this] using ih (n / 256) i h'

/-- **Every digit of the big-endian expansion, in closed form.** Index `i`
counts from the most significant end, so it names the `w - 1 - i`-th power. -/
lemma getElem_toBeBytesFixed (n w i : ℕ) (h : i < (toBeBytesFixed n w).length) :
    (toBeBytesFixed n w)[i] = UInt8.ofNat (n / 256 ^ (w - 1 - i) % 256) := by
  have hi : i < w := by simpa using h
  show (toLeBytesFixed n w).reverse[i]'(by simpa using hi) = _
  rw [List.getElem_reverse (by simp; omega), getElem_toLeBytesFixed]
  simp only [length_toLeBytesFixed]

/-- `getElem_toLeBytesFixed` with the byte read as a `ℕ`. -/
lemma toNat_getElem_toLeBytesFixed (n w i : ℕ) (h : i < (toLeBytesFixed n w).length) :
    ((toLeBytesFixed n w)[i]).toNat = n / 256 ^ i % 256 := by
  rw [getElem_toLeBytesFixed]
  simp

/-- `getElem_toBeBytesFixed` with the byte read as a `ℕ`. This is the form a
consumer working with a `List ℕ` of published bytes wants. -/
lemma toNat_getElem_toBeBytesFixed (n w i : ℕ) (h : i < (toBeBytesFixed n w).length) :
    ((toBeBytesFixed n w)[i]).toNat = n / 256 ^ (w - 1 - i) % 256 := by
  rw [getElem_toBeBytesFixed]
  simp

@[simp] lemma toLeBytesFixed_zero (w : ℕ) : toLeBytesFixed 0 w = List.replicate w 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [toLeBytesFixed, ih, List.replicate_succ]

/-- `zeroPadBytes` commutes with `cons` once the width has a successor to spend. -/
private lemma zeroPadBytes_cons (w : ℕ) (b : UInt8) (bs : List UInt8) :
    zeroPadBytes (w + 1) (b :: bs) = b :: zeroPadBytes w bs := by
  simp [zeroPadBytes]

/-- The equation for `toBytes'` at a successor, restated with `UInt8.ofNat` in
place of the raw `UInt8` constructor the definition uses. -/
private lemma toBytes'_succ (m : ℕ) :
    toBytes' (m + 1) = UInt8.ofNat ((m + 1) % 256) :: toBytes' ((m + 1) / 256) := by
  conv_lhs => unfold toBytes'
  refine congrArg (· :: _) ?_
  refine UInt8.toNat_inj.mp ?_
  show (m + 1) % UInt8.size = _
  simp [UInt8.size, Nat.mod_eq_of_lt (Nat.mod_lt (m + 1) (by norm_num : 0 < 256))]

/-- The one place `toBytes'` still appears: the variable-length private expansion
is the fixed-width public one with the leading zeroes dropped. -/
private lemma zeroPadBytes_toBytes' (w : ℕ) :
    ∀ n : ℕ, n < 256 ^ w → zeroPadBytes w (toBytes' n) = toLeBytesFixed n w := by
  induction w with
  | zero =>
    intro n h
    have hn : n = 0 := by simpa using h
    subst hn
    simp [toBytes', zeroPadBytes, toLeBytesFixed]
  | succ w ih =>
    intro n h
    match n with
    | 0 => simp [toBytes', zeroPadBytes, toLeBytesFixed, List.replicate_succ]
    | m + 1 =>
      have hlt : (m + 1) / 256 < 256 ^ w :=
        Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact h)
      rw [toBytes'_succ, zeroPadBytes_cons, ih _ hlt]
      rfl

/-- **The bridge.** The fixed-width big-endian expansion is the variable-length
one (`toBytesBigEndian`) left-padded with zeroes — which is exactly the shape
`UInt256.toByteArray` is built in. -/
theorem toBeBytesFixed_eq_zeroPad (n w : ℕ) (h : n < 256 ^ w) :
    toBeBytesFixed n w
      = List.replicate (w - (toBytesBigEndian n).length) 0 ++ toBytesBigEndian n := by
  unfold toBeBytesFixed
  rw [← zeroPadBytes_toBytes' w n h]
  simp [zeroPadBytes, toBytesBigEndian, List.reverse_append]

/-- `toBytes!` — the public 32-wide little-endian encoder — is `toLeBytesFixed`,
so its digits are given by `getElem_toLeBytesFixed`. -/
theorem toBytes!_eq_toLeBytesFixed (v : UInt256) :
    toBytes! v = toLeBytesFixed v.toNat 32 :=
  zeroPadBytes_toBytes' 32 v.toNat (by
    rw [show (256 : ℕ) ^ 32 = UInt256.size from by norm_num [UInt256.size]]
    exact v.val.isLt)

def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  .ofNat <| fromBytes' arr.data.toList.reverse

end EvmYul

section HicSuntDracones

def ByteArray.copySlice' (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  if false -- srcOff < 2^64 && destOff < 2^64 && len < 2^64
  then src.copySlice srcOff dest destOff len exact -- NB only when `srcOff`, `destOff` and `len` are sufficiently small
  else let srcData := src.data
       let destData := dest.data
       let sourceChunk := srcData.extract srcOff (srcOff + len)
       let destBegin := destData.extract 0 destOff
       let destEnd := destData.extract (destOff + len) destData.size
       ⟨destBegin ++ sourceChunk ++ destEnd⟩

end HicSuntDracones
