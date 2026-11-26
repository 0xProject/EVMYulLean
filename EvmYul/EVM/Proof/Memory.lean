import EvmYul.MachineStateOps

/-! # Memory read-over-write

`MachineState.memory` is a flat `ByteArray`, written through `ByteArray.write`
and read back through `ByteArray.readWithPadding`. `ByteArray.write` computes on
lists of bytes (`List.take`/`List.drop`/`List.replicate`), while
`ByteArray.readWithPadding` clamps the slice and appends zero padding. Neither
reduces directly to `Array.extract` splices, so proofs about `MSTORE`, `MSTORE8`,
and `RETURN` use the normal forms below.

This file supplies those normal forms and the lemmas built on them.

* `ByteArray.write_eq_of_fits` is the normal form: when the written span lies
  inside the destination, every padding term in `write` collapses and the result
  is the plain three-way splice `dest[0, a) ++ src ++ dest[a + len, size)`.
  `ByteArray.readWithPadding_eq_extract` is the matching normal form for the
  read side, where the padding is likewise empty.
* `ByteArray.write_eq_of_grows` is the normal form for a write that reaches the
  end of the destination or goes past it: `write` zero-extends the destination
  itself, so the result is `dest[0, destAddr) ++ 0…0 ++ src` and memory ends up
  `max dest.size (destAddr + len)` long (`ByteArray.size_write`).
* `ByteArray.readWithPadding_write_self` is read-over-write proper: reading back
  exactly the span that was just written returns the source.
  `readWithPadding_write_self_of_pad` is the same statement with no hypothesis
  about `dest.size` at all, by combining the two cases. Its two companions
  `readWithPadding_write_of_le` and `readWithPadding_write_of_ge` are the frame
  half — a read disjoint from the written span does not see the write.
* The `MachineState` layer specialises these to the operations the semantics
  actually dispatches on: `readWithPadding_memory_mstore8`,
  `readWithPadding_memory_mstore`, and `H_return_evmReturn_mstore`, which is the
  composite a `MSTORE`-then-`RETURN` fragment needs — the bytes a contract
  returns are the word it stored. Each has an `_of_le` variant that drops the
  in-bounds hypothesis, and `H_return_evmReturn_mstore_zero` drops it entirely.

Everything rests on `EvmYul.MachineStateOps` and the Lean core `ByteArray`
lemmas. No axiom is introduced and no proof is admitted.

## For consumers

`import EvmYul.EVM.Proof.Memory`. A proof that has to discharge a goal of the
shape `μ.memory.readWithPadding a l = …` wants, in rough order of usefulness:

| Goal shape | Lemma |
| --- | --- |
| `MSTORE(0, v)`; `RETURN(0, 32)` returns `v` | `EvmYul.MachineState.H_return_evmReturn_mstore_zero` |
| bytes returned after `MSTORE`; `RETURN` | `EvmYul.MachineState.H_return_evmReturn_mstore_of_le` |
| `H_return` of an `evmReturn` | `EvmYul.MachineState.H_return_evmReturn` |
| read back an `MSTORE`d word | `EvmYul.MachineState.readWithPadding_memory_mstore_of_le` |
| read back an `MSTORE8`d byte | `EvmYul.MachineState.readWithPadding_memory_mstore8_of_le` |
| `spos + 32` is in bounds after the store | `EvmYul.MachineState.le_size_memory_mstore` |
| memory size across a store | `EvmYul.MachineState.size_memory_mstore_of_pad` |
| read disjoint from a store | `ByteArray.readWithPadding_write_of_le` / `_of_ge` |
| generic read-over-write | `ByteArray.readWithPadding_write_self_of_pad` |
| unfold `write` / `readWithPadding` | `ByteArray.write_eq_of_fits` / `_of_grows` / `readWithPadding_eq_extract` |

`EvmYul.UInt256.size_toByteArray` (a stored word is exactly 32 bytes) is the
side condition most of the `MSTORE` lemmas need supplied at their call sites.

Every lemma above ends at `sval.toByteArray`, which says nothing about the bytes
themselves. To get *contents* rather than a `ByteArray`:

| Goal shape | Lemma |
| --- | --- |
| the 32 bytes of a stored word | `EvmYul.UInt256.toList_data_toByteArray` |
| one byte of a stored word, as `ℕ` | `EvmYul.UInt256.toNat_get!_toByteArray` |
| a stored word as a `List ℕ` | `EvmYul.UInt256.map_toNat_get!_toByteArray` |
| `MSTORE(0, v)`; `RETURN(0, 32)` as a `List ℕ` | `EvmYul.MachineState.map_toNat_get!_H_return_evmReturn_mstore_zero` |
| the same, one byte at a time | `EvmYul.MachineState.toNat_get!_H_return_evmReturn_mstore_zero` |

These bottom out in `EvmYul.toBeBytesFixed`, the public fixed-width big-endian
encoder in `EvmYul.UInt256`, whose digits are `EvmYul.getElem_toBeBytesFixed` /
`EvmYul.toNat_getElem_toBeBytesFixed`. `EvmYul.toBytesBigEndian` itself is built
from the private, well-founded `toBytes'` and cannot be unfolded downstream;
`EvmYul.toBeBytesFixed_eq_zeroPad` is the bridge that removes the need to.

## Where the in-bounds hypotheses come from

The `_of_fits` equations state the result with no padding term. That is correct
only when the span lies inside memory.

What supplies them is **the store, not the gas charge**. `MachineState.M` feeds
`activeWords` and provably leaves `memory` alone
(`MachineState.memory_activeWords_update`), so a frame that has charged expansion
for `[0, 32)` still has `memory.size = 0` and cannot satisfy
`spos.toNat + 32 ≤ μ.memory.size`. Frames start empty, so this is not a corner
case: it is what the canonical `MSTORE(0, v); RETURN(0, 32)` fragment looks like.

`write` closes the gap on its own, by zero-extending its destination. Hence
`le_size_memory_mstore`: `spos + 32 ≤ (μ.mstore spos sval).memory.size`, with no
assumption on `μ`. The `_of_le` and `_zero` lemmas are the read-side consequences,
and they are the ones to cite; the `_of_fits` originals are kept because they are
true and are the cheaper rewrite when a caller does already know the span fits.

The fork's `ByteArray.write` has no `USize` length, so no proof uses `hpad`.
It stays in the `_of_pad` signatures so that the statements match upstream.

## The opcode layer

Everything here is stated about the `MachineState` operations. A correspondence
proof holds an `EvmYul.EVM.step` on a full `EVM.State` instead, and must first
know that the step ran `MachineState.mstore`. `EvmYul.EVM.Proof.MemoryStep`
supplies that link and restates the results above one layer up — in particular
`le_size_memory_step_MSTORE` (in bounds after a real `MSTORE`) and
`H_return_step_MSTORE_RETURN_zero` (the canonical two-opcode residual).
-/

set_option autoImplicit false

namespace ffi.ByteArray

/-- `zeroes` is `Array.replicate` behind an `@[extern]`, so it has the requested size. Stated
against `USize.toNat` rather than a specific `Nat`-cast spelling of the argument, because the
padding length inside `ByteArray.readWithPadding` can normalize in more than one way. -/
@[simp] theorem size_zeroes (u : USize) : (ffi.ByteArray.zeroes u).size = u.toNat := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- Padding by zero bytes is padding by nothing. -/
theorem zeroes_eq_empty {u : USize} (h : u.toNat = 0) :
    ffi.ByteArray.zeroes u = ByteArray.empty := by
  ext1; simp [ffi.ByteArray.zeroes, h]

/-- Recover `n` from a `USize` cast when `n < 2 ^ System.Platform.numBits`. -/
theorem toNat_natCast_of_lt (n : ℕ) (h : n < 2 ^ System.Platform.numBits) :
    ({ toBitVec := (n : BitVec System.Platform.numBits) } : USize).toNat = n := by
  simp only [USize.toNat, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Recover `32 - n` from a `USize` subtraction when `n ≤ 32`. -/
theorem toNat_usizeSub_of_le (n : ℕ) (h : n ≤ 32) :
    ({ toBitVec := (32 : BitVec System.Platform.numBits)
        - (n : BitVec System.Platform.numBits) } : USize).toNat = 32 - n := by
  have hw : 32 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  have hn : n < 2 ^ System.Platform.numBits := by omega
  have h32 : (32 : BitVec System.Platform.numBits).toNat = 32 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h32]
  rw [show 2 ^ System.Platform.numBits - n + 32
        = 2 ^ System.Platform.numBits + (32 - n) from by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

end ffi.ByteArray

namespace ByteArray

@[simp] theorem self_append_empty (b : ByteArray) : b ++ ByteArray.empty = b := by ext1; simp

@[simp] theorem empty_append_self (b : ByteArray) : ByteArray.empty ++ b = b := by ext1; simp

/-- Appending zero padding is a no-op. Phrased on `USize.toNat` so that `simp` discharges it
regardless of how the padding length was spelled. -/
theorem append_zeroes {b : ByteArray} {u : USize} (h : u.toNat = 0) :
    b ++ ffi.ByteArray.zeroes u = b := by
  rw [ffi.ByteArray.zeroes_eq_empty h, self_append_empty]

/-! ## Splicing

`write_eq_of_fits` produces a three-way `Array` append, and the read lemmas then
have to extract a span out of it. These are the three span positions. -/

/-- The middle summand of a three-way append is exactly what sits at its offset. -/
theorem _root_.Array.extract_append_middle (A B C : Array UInt8) (i j : ℕ)
    (hi : i = A.size) (hj : j = A.size + B.size) :
    (A ++ B ++ C).extract i j = B := by
  subst hi; subst hj; apply Array.ext'; simp

/-- A span ending inside the first summand only sees the first summand. -/
theorem _root_.Array.extract_append_of_le (A B C : Array UInt8) (i j : ℕ) (h : j ≤ A.size) :
    (A ++ B ++ C).extract i j = A.extract i j := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_append, List.extract_eq_take_drop,
    List.append_assoc, ← List.drop_take]
  rw [List.take_append_of_le_length (by simpa using h)]

/-- A span starting past the middle summand only sees the last summand. -/
theorem _root_.Array.extract_append_of_ge (A B C : Array UInt8) (i j : ℕ)
    (hij : i ≤ j) (h : A.size + B.size ≤ i) :
    (A ++ B ++ C).extract i j = C.extract (i - (A.size + B.size)) (j - (A.size + B.size)) := by
  apply Array.ext'
  simp only [Array.toList_extract, Array.toList_append, List.extract_eq_take_drop,
    List.append_assoc]
  rw [List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
      show j - (A.size + B.size) - (i - (A.size + B.size)) = j - i from by omega]
  simp [Nat.sub_sub]

/-- The last summand of a two-way append is exactly what sits at its offset.
A `write` that grows the destination produces `prefix ++ src` rather than the
three-way splice, because there is no tail left to keep. -/
theorem _root_.Array.extract_append_tail (A B : Array UInt8) (i j : ℕ)
    (hi : i = A.size) (hj : j = A.size + B.size) :
    (A ++ B).extract i j = B := by
  subst hi; subst hj; rw [Array.extract_append_right, Array.extract_size]

/-- Taking the first `n` elements of `A ++ Z` when `Z` has length `n - A.size` yields
`A.extract 0 n ++ Z`. -/
theorem _root_.Array.extract_zero_append (A Z : Array UInt8) (n : ℕ)
    (hZ : Z.size = n - A.size) :
    (A ++ Z).extract 0 n = A.extract 0 n ++ Z := by
  rcases Nat.le_total n A.size with h | h
  · rw [Array.eq_empty_of_size_eq_zero (by omega : Z.size = 0)]
    simp
  · rw [Array.extract_eq_self_of_le (by simp; omega),
        Array.extract_eq_self_of_le h]

/-! ## Normal forms -/

/-- **`write` reduced.** Writing the whole of `src` at `destAddr`, with the span
inside `dest`, is the three-way splice. Every zero-padding term in the
definition of `write` has length `0` under these hypotheses. -/
theorem write_eq_of_fits (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size) :
    ByteArray.write src 0 dest destAddr len
      = ⟨dest.data.extract 0 destAddr ++ src.data
          ++ dest.data.extract (destAddr + len) dest.size⟩ := by
  have hsd : src.data.toList.length = len := by
    rw [Array.length_toList]; exact hsrc
  have hdl : dest.data.toList.length = dest.size := Array.length_toList
  unfold ByteArray.write
  rw [ite_eq_right (by omega)]
  ext1
  apply Array.ext'
  simp only [List.drop_zero, List.take_of_length_le (Nat.le_of_eq hsd), hsd, hdl, Nat.sub_self,
    List.replicate_zero, List.append_nil, Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, Nat.sub_zero]
  rw [show destAddr - dest.size = 0 from by omega, List.replicate_zero, List.append_nil]
  congr 1
  exact (List.take_of_length_le (by rw [List.length_drop, hdl])).symm

/-- An in-bounds write does not resize the destination. -/
theorem size_write_of_fits (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).size = dest.size := by
  rw [write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  show (_ : Array UInt8).size = _
  simp only [Array.size_append, Array.size_extract, ByteArray.size_data]
  have hs : src.data.size = len := by simpa using hsrc
  omega

/-- **`write` reduced, growing case.** When the written span reaches the end of
`dest` or past it, `write` zero-extends `dest` up to `destAddr` and appends `src`,
so there is no tail to keep and the result is `dest[0, destAddr) ++ 0…0 ++ src`.

A fresh frame is in this case. `MachineState.M` charges expansion into
`activeWords` and leaves `memory` alone, so a frame that has only ever charged
gas still has `memory.size = 0`; it is `write` itself, not the charge, that makes
memory big enough to read back from. -/
theorem write_eq_of_grows (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hcov : dest.size ≤ destAddr + len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    ByteArray.write src 0 dest destAddr len
      = ⟨dest.data.extract 0 destAddr ++ Array.replicate (destAddr - dest.size) 0
          ++ src.data⟩ := by
  have _ := hpad
  have hsd : src.data.toList.length = len := by
    rw [Array.length_toList]; exact hsrc
  have hdl : dest.data.toList.length = dest.size := Array.length_toList
  unfold ByteArray.write
  rw [ite_eq_right (by omega)]
  ext1
  apply Array.ext'
  simp only [List.drop_zero, List.take_of_length_le (Nat.le_of_eq hsd), hsd, hdl, Nat.sub_self,
    List.replicate_zero, List.append_nil, Array.toList_append, Array.toList_extract,
    Array.toList_replicate, List.extract_eq_take_drop, Nat.sub_zero]
  rw [List.drop_eq_nil_of_le (by rw [hdl]; exact hcov), List.append_nil, List.take_append, hdl,
      List.take_replicate, Nat.min_self]

/-- **How far a `write` grows its destination.** Combined with
`size_write_of_fits`, this is the fact a caller needs in order to know that a
later read is in bounds: after writing `len` bytes at `destAddr`, memory is at
least `destAddr + len` long, whatever it was before. -/
theorem size_write (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).size = max dest.size (destAddr + len) := by
  rcases Nat.lt_or_ge (destAddr + len) dest.size with h | h
  · rw [size_write_of_fits src dest destAddr len hlen hsrc (by omega)]
    omega
  · rw [write_eq_of_grows src dest destAddr len hlen hsrc h hpad]
    show (_ : Array UInt8).size = _
    have hsd : src.data.size = len := by simpa using hsrc
    simp only [Array.size_append, Array.size_extract, Array.size_replicate,
      ByteArray.size_data, hsd]
    omega

/-- **`readWithPadding` reduced.** An in-bounds read needs no padding and no
clamping, so it is a plain `extract`. -/
theorem readWithPadding_eq_extract (source : ByteArray) (addr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hfit : addr + len ≤ source.size) :
    source.readWithPadding addr len = source.extract addr (addr + len) := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [ite_eq_right (by omega)]
  simp only []
  rw [ite_eq_right (by omega), show min len (source.size - addr) = len from by omega]
  have hEq : (⟨⟨(source.data.toList.drop addr).take len⟩⟩ : ByteArray) =
      source.extract addr (addr + len) := by
    ext1
    apply Array.ext'
    simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
    rw [show addr + len - addr = len from by omega]
  rw [hEq]
  have hsize : (source.extract addr (addr + len)).size = len := by
    simp; omega
  rw [hsize, append_zeroes (by simp)]

/-! ## Read-over-write

The three cases of a read against a write: the read span is the written span, or
it lies entirely below it, or entirely above it. -/

/-- **Read-over-write.** Reading back exactly the span that was written returns
the source. -/
theorem readWithPadding_write_self (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hfit : destAddr + len ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  rw [readWithPadding_eq_extract _ _ _ hlen hlen64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  have hB : src.data.size = len := by simpa using hsrc
  ext1
  simp only [ByteArray.data_extract]
  exact Array.extract_append_middle _ _ _ _ _ hA.symm (by omega)

/-- **Read-over-write, growing case.** Reading back a span that the write had to
grow memory to hold still returns the source. -/
theorem readWithPadding_write_self_of_grows (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hcov : dest.size ≤ destAddr + len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  have hsz := size_write src dest destAddr len hlen hsrc hpad
  have hsd : src.data.size = len := by simpa using hsrc
  rw [readWithPadding_eq_extract _ _ _ hlen hlen64 (by omega),
      write_eq_of_grows src dest destAddr len hlen hsrc hcov hpad]
  have hP : (dest.data.extract 0 destAddr
      ++ Array.replicate (destAddr - dest.size) (0 : UInt8)).size = destAddr := by
    simp only [Array.size_append, Array.size_extract, Array.size_replicate,
      ByteArray.size_data, Nat.sub_zero]
    omega
  ext1
  simp only [ByteArray.data_extract]
  exact Array.extract_append_tail _ _ _ _ hP.symm (by omega)

/-- **Read-over-write, no bound on the destination.** The union of the in-bounds
and growing cases: reading back the span that was written returns the source
whatever `dest.size` was. The fork's `ByteArray.write` has no `USize` length, so
no proof uses `hpad`; it stays so that the statement matches upstream. -/
theorem readWithPadding_write_self_of_pad (src dest : ByteArray) (destAddr len : ℕ)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) (hsrc : src.size = len)
    (hpad : destAddr - dest.size < 2 ^ System.Platform.numBits) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding destAddr len = src := by
  rcases Nat.lt_or_ge (destAddr + len) dest.size with h | h
  · exact readWithPadding_write_self src dest destAddr len hlen hlen64 hsrc (by omega)
  · exact readWithPadding_write_self_of_grows src dest destAddr len hlen hlen64 hsrc h hpad

/-- **Frame, below.** A read entirely below the written span is unaffected. -/
theorem readWithPadding_write_of_le (src dest : ByteArray) (destAddr len a l : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size)
    (hl : 0 < l) (hl64 : l < 2 ^ 64) (hbelow : a + l ≤ destAddr) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding a l
      = dest.readWithPadding a l := by
  rw [readWithPadding_eq_extract _ _ _ hl hl64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      readWithPadding_eq_extract _ _ _ hl hl64 (by omega),
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  ext1
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_le _ _ _ _ _ (by omega)]
  apply Array.ext'
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero]
  rw [Nat.sub_zero, List.drop_take, List.take_take,
      show min (a + l - a) (destAddr - a) = a + l - a from by omega]

/-- **Frame, above.** A read entirely above the written span is unaffected. -/
theorem readWithPadding_write_of_ge (src dest : ByteArray) (destAddr len a l : ℕ)
    (hlen : 0 < len) (hsrc : src.size = len) (hfit : destAddr + len ≤ dest.size)
    (hl : 0 < l) (hl64 : l < 2 ^ 64) (habove : destAddr + len ≤ a)
    (hend : a + l ≤ dest.size) :
    (ByteArray.write src 0 dest destAddr len).readWithPadding a l
      = dest.readWithPadding a l := by
  rw [readWithPadding_eq_extract _ _ _ hl hl64
        (by rw [size_write_of_fits src dest destAddr len hlen hsrc hfit]; omega),
      readWithPadding_eq_extract _ _ _ hl hl64 hend,
      write_eq_of_fits src dest destAddr len hlen hsrc hfit]
  have hA : (dest.data.extract 0 destAddr).size = destAddr := by
    simp only [Array.size_extract, ByteArray.size_data]
    omega
  have hB : src.data.size = len := by simpa using hsrc
  ext1
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_ge _ _ _ _ _ (by omega) (by omega), hA, hB]
  apply Array.ext'
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  rw [show a + l - (destAddr + len) - (a - (destAddr + len)) = l from by omega,
      show a + l - a = l from by omega, List.drop_take, List.drop_drop,
      show destAddr + len + (a - (destAddr + len)) = a from by omega,
      List.take_take,
      show min l (dest.size - (destAddr + len) - (a - (destAddr + len))) = l from by omega]

end ByteArray

namespace EvmYul

/-- `UInt256.toByteArray` always produces 32 bytes: the big-endian expansion has
length at most 32 (`toBytesBigEndian_UInt256_len_le`) and the definition
left-pads to make up the difference. -/
theorem UInt256.size_toByteArray (v : UInt256) : (UInt256.toByteArray v).size = 32 :=
  UInt256.toByteArray_size v

/-! ## What is *in* a stored word

`size_toByteArray` says a stored word is 32 bytes wide; the lemmas below say
which 32 bytes. `UInt256.toByteArray` left-pads `toBytesBigEndian v.toNat` with
zeroes to 32 bytes, and `EvmYul.toBeBytesFixed_eq_zeroPad` says the fixed-width
big-endian expansion has that exact shape, so the two agree byte for byte.
Nothing here unfolds the private `toBytes'`: the padding structure comes from
`toBeBytesFixed_eq_zeroPad` and the digits from `getElem_toBeBytesFixed`. -/

/-- **The contents of a stored word**, as a list. -/
theorem UInt256.toList_data_toByteArray (v : UInt256) :
    (UInt256.toByteArray v).data.toList = toBeBytesFixed v.toNat 32 := by
  have hlt : v.toNat < 256 ^ 32 := by
    rw [show (256 : ℕ) ^ 32 = UInt256.size from by norm_num [UInt256.size]]
    exact v.val.isLt
  rw [toBeBytesFixed_eq_zeroPad v.toNat 32 hlt, UInt256.toByteArray_data_toList]

/-- **A single byte of a stored word**, read out with `ByteArray.get!` and as a
`ℕ`. Index `i` counts from the most significant end, so it names the `31 - i`-th
base-256 digit. -/
theorem UInt256.toNat_get!_toByteArray (v : UInt256) (i : ℕ) (h : i < 32) :
    ((UInt256.toByteArray v).get! i).toNat = v.toNat / 256 ^ (31 - i) % 256 := by
  have hlist : i < (UInt256.toByteArray v).data.toList.length := by
    rw [UInt256.toList_data_toByteArray, length_toBeBytesFixed]; exact h
  have hidx : i < (UInt256.toByteArray v).data.size := by
    rwa [← Array.length_toList]
  show ((UInt256.toByteArray v).data[i]!).toNat = _
  rw [getElem!_pos (UInt256.toByteArray v).data i hidx, ← Array.getElem_toList hidx]
  rw [List.getElem_of_eq (UInt256.toList_data_toByteArray v) hlist,
      toNat_getElem_toBeBytesFixed]

/-- **The contents of a stored word, in the shape a `List ℕ` observation takes.**
`(List.range size).map (fun i ↦ (get! i).toNat)` is how a consumer that publishes
bytes as naturals reads a `ByteArray`; this pins that list to the base-256 digits
of the word, with no `ByteArray` and no `UInt256` left in it. -/
theorem UInt256.map_toNat_get!_toByteArray (v : UInt256) :
    (List.range (UInt256.toByteArray v).size).map
        (fun i => ((UInt256.toByteArray v).get! i).toNat)
      = (List.range 32).map (fun i => v.toNat / 256 ^ (32 - 1 - i) % 256) := by
  rw [UInt256.size_toByteArray]
  refine List.ext_getElem (by simp) fun i h₁ _ => ?_
  have hi : i < 32 := by simpa using h₁
  simpa using UInt256.toNat_get!_toByteArray v i hi

namespace MachineState

/-! ## The `MachineState` layer

`mstore8` writes one byte and `mstore` writes a 32-byte big-endian word; both go
through `writeBytes`, hence through `ByteArray.write` at source offset `0`. -/

/-- Reading back the byte written by `MSTORE8`. -/
theorem readWithPadding_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.readWithPadding spos.toNat 1
      = ⟨#[UInt8.ofNat sval.toNat]⟩ := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self _ _ _ _ (by omega) (by norm_num) rfl hfit

/-- An in-bounds `MSTORE8` does not resize memory. -/
theorem size_memory_mstore8 (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 1 ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.size = μ.memory.size := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).size = _
  exact ByteArray.size_write_of_fits _ _ _ _ (by omega) rfl hfit

/-- **Reading back the word written by `MSTORE`.** -/
theorem readWithPadding_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self _ _ _ _ (by omega) (by norm_num)
    (UInt256.size_toByteArray sval) hfit

/-- An in-bounds `MSTORE` does not resize memory. -/
theorem size_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.size = μ.memory.size := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).size = _
  exact ByteArray.size_write_of_fits _ _ _ _ (by omega) (UInt256.size_toByteArray sval) hfit

/-! ## Charged expansion is not an in-bounds hypothesis

`MachineState.M` is a `ℕ → ℕ → ℕ → ℕ` that every memory opcode feeds into
`activeWords`. It does not touch `memory`, so a frame that has charged expansion
for `[0, 32)` still has `memory.size = 0`. The lemmas below therefore do *not*
route through `M`; they get their in-bounds facts from the write itself. -/

/-- Updating `activeWords` — which is all that charging expansion via
`MachineState.M` ever does — leaves `memory` unchanged. Consequently `M` cannot
discharge a hypothesis about `memory.size`; see `size_memory_mstore_of_pad` for
what actually does. -/
theorem memory_activeWords_update (μ : MachineState) (n : UInt256) :
    ({ μ with activeWords := n } : MachineState).memory = μ.memory := rfl

/-- **How far an `MSTORE` grows memory.** After storing a word at `spos`, memory
has size `max μ.memory.size (spos.toNat + 32)`. Therefore
`spos.toNat + 32 ≤ (μ.mstore spos sval).memory.size`, which is the in-bounds
fact a following `RETURN` or `MLOAD` needs. -/
theorem size_memory_mstore_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore spos sval).memory.size = max μ.memory.size (spos.toNat + 32) := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).size = _
  exact ByteArray.size_write _ _ _ _ (by omega) (UInt256.size_toByteArray sval) hpad

/-- **The in-bounds fact, established after the store rather than before it.**
This is the direct replacement for an appeal to charged expansion: `MSTORE` makes
its own span readable. -/
theorem le_size_memory_mstore (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    spos.toNat + 32 ≤ (μ.mstore spos sval).memory.size := by
  rw [size_memory_mstore_of_pad μ spos sval hpad]
  omega

/-- `MSTORE8` likewise grows memory to cover the byte it wrote. -/
theorem size_memory_mstore8_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore8 spos sval).memory.size = max μ.memory.size (spos.toNat + 1) := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).size = _
  exact ByteArray.size_write _ _ _ _ (by omega) rfl hpad

/-- **Reading back an `MSTORE8`d byte, no padding parameter.** -/
theorem readWithPadding_memory_mstore8_of_le (μ : MachineState) (spos sval : UInt256)
    (hstart : spos.toNat ≤ μ.memory.size) :
    (μ.mstore8 spos sval).memory.readWithPadding spos.toNat 1
      = ⟨#[UInt8.ofNat sval.toNat]⟩ := by
  show (ByteArray.write ⟨#[UInt8.ofNat sval.toNat]⟩ 0 μ.memory spos.toNat 1).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by omega) (by norm_num) rfl
    (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)

/-- **Reading back an `MSTORE`d word without knowing how big memory was.** -/
theorem readWithPadding_memory_mstore_of_pad (μ : MachineState) (spos sval : UInt256)
    (hpad : spos.toNat - μ.memory.size < 2 ^ System.Platform.numBits) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray := by
  show (ByteArray.write sval.toByteArray 0 μ.memory spos.toNat 32).readWithPadding _ _ = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by omega) (by norm_num)
    (UInt256.size_toByteArray sval) hpad

/-- **Reading back an `MSTORE`d word, no padding parameter.** A store starting at
or before the current end of memory discharges the `hpad` parameter automatically.
Fresh frames (`memory.size = 0`, `spos = 0`) are the main instance. -/
theorem readWithPadding_memory_mstore_of_le (μ : MachineState) (spos sval : UInt256)
    (hstart : spos.toNat ≤ μ.memory.size) :
    (μ.mstore spos sval).memory.readWithPadding spos.toNat 32 = sval.toByteArray :=
  readWithPadding_memory_mstore_of_pad μ spos sval
    (by rw [show spos.toNat - μ.memory.size = 0 from by omega]; positivity)

/-! ## The `RETURN` bridge

`evmReturn` is the only thing standing between memory and the bytes a halting
`X` hands back: `H` reads `H_return` and returns it verbatim. -/

/-- `RETURN` publishes a padded read of memory, and touches nothing else that a
read depends on. -/
theorem H_return_evmReturn (μ : MachineState) (mstart s : UInt256) :
    (μ.evmReturn mstart s).H_return = μ.memory.readWithPadding mstart.toNat s.toNat := rfl

/-- **`MSTORE` then `RETURN`.** The bytes returned by a fragment that stores a
word and returns exactly that word are the word itself. This is the composite
shape a straight-line `MSTORE`/`RETURN` correspondence proof reduces to. -/
theorem H_return_evmReturn_mstore (μ : MachineState) (spos sval s : UInt256)
    (hs : s.toNat = 32) (hfit : spos.toNat + 32 ≤ μ.memory.size) :
    ((μ.mstore spos sval).evmReturn spos s).H_return = sval.toByteArray := by
  rw [H_return_evmReturn, hs]
  exact readWithPadding_memory_mstore μ spos sval hfit

/-- **`MSTORE` then `RETURN`, without a prior in-bounds hypothesis.** Same
composite as `H_return_evmReturn_mstore`, but asking only that the store start at
or before the current end of memory rather than that the whole span already fit.
This is the version a real caller can discharge: `H_return_evmReturn_mstore`'s
`hfit` cannot be obtained from charging expansion, because
`memory_activeWords_update` says the charge does not touch `memory`. -/
theorem H_return_evmReturn_mstore_of_le (μ : MachineState) (spos sval s : UInt256)
    (hs : s.toNat = 32) (hstart : spos.toNat ≤ μ.memory.size) :
    ((μ.mstore spos sval).evmReturn spos s).H_return = sval.toByteArray := by
  rw [H_return_evmReturn, hs]
  exact readWithPadding_memory_mstore_of_le μ spos sval hstart

/-- **The canonical fragment, hypothesis-free.** `MSTORE(0, v)` then
`RETURN(0, 32)` returns `v`, for *any* starting machine state — in particular for
a fresh frame, where `memory.size = 0`. This is the residual shape an
`EndpointAgrees`-style correspondence proof is left with once the `CfgState` side
has been discharged, and it needs nothing about memory going in. -/
theorem H_return_evmReturn_mstore_zero (μ : MachineState) (sval s : UInt256)
    (hs : s.toNat = 32) :
    ((μ.mstore ⟨0⟩ sval).evmReturn ⟨0⟩ s).H_return = sval.toByteArray :=
  H_return_evmReturn_mstore_of_le μ ⟨0⟩ sval s hs (by
    show (0 : ℕ) ≤ _
    exact Nat.zero_le _)

/-! ## The residual with the word opened up

The lemmas above end at `sval.toByteArray`, which is opaque. Composing them with
`UInt256.toList_data_toByteArray` and `UInt256.map_toNat_get!_toByteArray` ends
them at the base-256 digits of `sval` instead, which is what a correspondence
proof against an abstract big-endian encoder actually has to match. -/

/-- Reading back an `MSTORE`d word, as bytes rather than as a `ByteArray`. -/
theorem toList_data_readWithPadding_memory_mstore_of_le
    (μ : MachineState) (spos sval : UInt256) (hstart : spos.toNat ≤ μ.memory.size) :
    ((μ.mstore spos sval).memory.readWithPadding spos.toNat 32).data.toList
      = toBeBytesFixed sval.toNat 32 := by
  rw [readWithPadding_memory_mstore_of_le μ spos sval hstart,
      UInt256.toList_data_toByteArray]

/-- **`MSTORE(0, v)` then `RETURN(0, 32)`, byte by byte.** No hypothesis about
memory, and no `UInt256` or `ByteArray` on the right: the `i`-th published byte
is the `31 - i`-th base-256 digit of the stored word. -/
theorem toNat_get!_H_return_evmReturn_mstore_zero (μ : MachineState) (sval s : UInt256)
    (hs : s.toNat = 32) (i : ℕ) (hi : i < 32) :
    ((((μ.mstore ⟨0⟩ sval).evmReturn ⟨0⟩ s).H_return).get! i).toNat
      = sval.toNat / 256 ^ (31 - i) % 256 := by
  rw [H_return_evmReturn_mstore_zero μ sval s hs]
  exact UInt256.toNat_get!_toByteArray sval i hi

/-- **The same residual as a `List ℕ`.** This is the shape a consumer that
observes return data as `(List.range size).map (fun i ↦ (get! i).toNat)` is left
with, with the encoding fully computed. -/
theorem map_toNat_get!_H_return_evmReturn_mstore_zero (μ : MachineState) (sval s : UInt256)
    (hs : s.toNat = 32) :
    (List.range ((μ.mstore ⟨0⟩ sval).evmReturn ⟨0⟩ s).H_return.size).map
        (fun i => (((μ.mstore ⟨0⟩ sval).evmReturn ⟨0⟩ s).H_return.get! i).toNat)
      = (List.range 32).map (fun i => sval.toNat / 256 ^ (32 - 1 - i) % 256) := by
  rw [H_return_evmReturn_mstore_zero μ sval s hs]
  exact UInt256.map_toNat_get!_toByteArray sval

end MachineState

end EvmYul
