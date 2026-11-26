import EvmYul.UInt256
import EvmYul.FFI.ffi

namespace EvmYul

namespace Specs

/-- Selectable Keccak-256 execution backend: pure kernel-reducible specification vs runtime C FFI. -/
inductive HashBackend where
  | PureKernel
  | RuntimeFFI
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Keccak-256 sponge rate in bytes (`1088 / 8 = 136`). -/
def rateBytes : ℕ := 136

/-- Keccak-256 digest size in bytes (`256 / 8 = 32`). -/
def digestBytes : ℕ := 32

/-- Keccak-f[1600] 24 round constants. -/
def roundConstants : List UInt64 :=
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
  , 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
  , 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
  , 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
  , 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
  , 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
  ]

/-- 64-bit left circular rotation (`rotl64`). -/
def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  let s := n % 64
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

/-- Extract the memory slice `[offset, offset + size)` hashed by `KECCAK256` (`0x20`).
    When `size = 0`, EVM `KECCAK256` hashes `ByteArray.empty` without reading memory. -/
def extractKeccakMemorySlice (mem : ByteArray) (offset size : ℕ) : ByteArray :=
  if size = 0 then ByteArray.empty else mem.extract offset (offset + size)

/-- Total, pure specification of EVM `KECCAK256` over a memory slice parameterized by a digest function. -/
def evalKeccak256SliceWith (hashFn : ByteArray → ByteArray) (mem : ByteArray) (offset size : ℕ) : ByteArray :=
  hashFn (extractKeccakMemorySlice mem offset size)

/-- Runtime FFI-backed `KECCAK256` slice evaluation (`ffi.KEC`). -/
def keccak256MemorySliceFFI (mem : ByteArray) (offset size : ℕ) : ByteArray :=
  evalKeccak256SliceWith ffi.KEC mem offset size

/-- Theorem 1: For `size = 0`, `extractKeccakMemorySlice` always returns `ByteArray.empty`
    independently of `mem` and `offset`. -/
theorem extractKeccakMemorySlice_zero_size (mem : ByteArray) (offset : ℕ) :
    extractKeccakMemorySlice mem offset 0 = ByteArray.empty := by
  rfl

/-- Theorem 2: For `size = 0`, any hash backend `hashFn` evaluates `evalKeccak256SliceWith`
    to `hashFn ByteArray.empty` regardless of `mem` and `offset`. -/
theorem evalKeccak256SliceWith_zero_size (hashFn : ByteArray → ByteArray) (mem₁ mem₂ : ByteArray) (off₁ off₂ : ℕ) :
    evalKeccak256SliceWith hashFn mem₁ off₁ 0 = evalKeccak256SliceWith hashFn mem₂ off₂ 0 := by
  rfl

/-- Theorem 3: If a pure kernel hash function `pureHash` agrees with `ffi.KEC` on all `ByteArray` inputs,
    then their memory-slice `KECCAK256` evaluations are extensionally equal for all `(mem, offset, size)`. -/
theorem evalKeccak256SliceWith_backend_equiv
    (pureHash : ByteArray → ByteArray)
    (hAgree : ∀ msg : ByteArray, pureHash msg = ffi.KEC msg)
    (mem : ByteArray) (offset size : ℕ) :
    evalKeccak256SliceWith pureHash mem offset size = keccak256MemorySliceFFI mem offset size := by
  unfold keccak256MemorySliceFFI evalKeccak256SliceWith
  exact hAgree (extractKeccakMemorySlice mem offset size)

/-- Theorem 4: Keccak-f[1600] defines exactly 24 round constants. -/
theorem roundConstants_length : roundConstants.length = 24 := by
  rfl

/-- Theorem 5: Keccak-256 rate (`136` bytes = `1088` bits) plus capacity (`64` bytes = `512` bits)
    equals the 200-byte (`1600`-bit) state width. -/
theorem rate_plus_capacity_bytes : rateBytes + 2 * digestBytes = 200 := by
  rfl

/-- Theorem 6: `rotl64 x 0 = x` for every 64-bit lane word `x`. -/
theorem rotl64_zero (x : UInt64) : rotl64 x 0 = x := by
  rfl

end Specs

end EvmYul
