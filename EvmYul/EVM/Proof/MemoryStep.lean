import EvmYul.EVM.Proof.Execution
import EvmYul.EVM.Proof.Memory

/-! # Memory read-over-write along the real opcode path

`EvmYul.EVM.Proof.Memory` states read-over-write for `MachineState.mstore`,
`MachineState.mstore8` and `MachineState.evmReturn` — the *implementations* of the
memory opcodes. A correspondence proof does not get to apply those directly: it
has an `EvmYul.EVM.step`, i.e. a `Step`/`StepOk` on a full `EVM.State`, and must
first know which `MachineState` operation that step actually ran.

This file supplies that last link. `MSTORE`, `MSTORE8` and `RETURN` are all
handled by the catch-all branch of `EvmYul.EVM.step`, which hands the state — with
this instruction's gas already deducted and `execLength` bumped, i.e. exactly
`stepPre` — to `EvmYul.step`, and thence to `EVM.binaryMachineStateOp`. So each
of `step_MSTORE`, `step_MSTORE8` and `step_RETURN` computes the post-state of one
real opcode, and the corollaries below read memory back out of it.

## What discharges the in-bounds side condition

The `Memory` lemmas that mention `μ.memory.size` are stated about the state
*before* the write, and a caller generally cannot prove them: frames start at
`memory.size = 0`, and charging memory expansion does not help, because
`MachineState.M` only ever updates `activeWords`
(`MachineState.memory_activeWords_update`, and `Z_ok_memory` for the charge that
`Z` performs). `activeWords_step_MSTORE` below records that the real opcode does
charge `M`, and `memory_step_MSTORE_eq` records that this charge leaves `memory`
untouched — so `M` is genuinely not a source of in-bounds facts.

The fact is instead produced by the store itself: `ByteArray.write` zero-extends
its destination, so `MSTORE` makes its own span readable. `le_size_memory_step_MSTORE`
is the resulting statement — `μ₀.toNat + 32 ≤ post.memory.size` holds *after* the
opcode, with no hypothesis about memory beforehand. That is what a following
`RETURN` or `MLOAD` needs, and it is what the canonical residual
`H_return_step_MSTORE_RETURN_zero` runs on.

No axiom is introduced and no proof is admitted.
-/

namespace EvmYul.EVM.Proof

open EvmYul EvmYul.EVM

/-! ## Reaching `EvmYul.step`

The three opcodes of interest carry no special case in `EvmYul.EVM.step`'s match,
so they take the final branch, which is definitionally `EvmYul.step` applied to
`stepPre`. -/

/-- `MSTORE` is dispatched to `EvmYul.step` on `stepPre`. -/
theorem step_eq_MSTORE (fuel gasCost : ℕ) (pre : State) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.MSTORE, none)) pre
      = EvmYul.step (τ := .EVM) .MSTORE none (stepPre gasCost pre) := rfl

/-- `MSTORE8` is dispatched to `EvmYul.step` on `stepPre`. -/
theorem step_eq_MSTORE8 (fuel gasCost : ℕ) (pre : State) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.MSTORE8, none)) pre
      = EvmYul.step (τ := .EVM) .MSTORE8 none (stepPre gasCost pre) := rfl

/-- `RETURN` is dispatched to `EvmYul.step` on `stepPre`. -/
theorem step_eq_RETURN (fuel gasCost : ℕ) (pre : State) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.RETURN, none)) pre
      = EvmYul.step (τ := .EVM) .RETURN none (stepPre gasCost pre) := rfl

/-! ## The three steps

`stepPre` touches `gasAvailable` and `execLength` only, so the memory-relevant
part of each post-state is the corresponding `MachineState` operation applied to
`pre`'s memory. -/

/-- **One `MSTORE` opcode.** Pops the offset and the value and stores the word;
the post-state is `pre` with gas charged, `execLength` bumped, the word written,
and the two operands gone from the stack. -/
theorem step_MSTORE (fuel gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256)
    (hpop : pre.stack.pop2 = some (s, μ₀, μ₁)) :
    StepOk (fuel + 1) gasCost (.MSTORE, none) pre
      (EVM.State.replaceStackAndIncrPC
        { stepPre gasCost pre with
            toMachineState := (stepPre gasCost pre).toMachineState.mstore μ₀ μ₁ } s) := by
  show EvmYul.step (τ := .EVM) .MSTORE none (stepPre gasCost pre) = _
  show EVM.binaryMachineStateOp MachineState.mstore (stepPre gasCost pre) = _
  unfold EVM.binaryMachineStateOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, hpop]
  rfl

/-- **One `MSTORE8` opcode.** -/
theorem step_MSTORE8 (fuel gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256)
    (hpop : pre.stack.pop2 = some (s, μ₀, μ₁)) :
    StepOk (fuel + 1) gasCost (.MSTORE8, none) pre
      (EVM.State.replaceStackAndIncrPC
        { stepPre gasCost pre with
            toMachineState := (stepPre gasCost pre).toMachineState.mstore8 μ₀ μ₁ } s) := by
  show EvmYul.step (τ := .EVM) .MSTORE8 none (stepPre gasCost pre) = _
  show EVM.binaryMachineStateOp MachineState.mstore8 (stepPre gasCost pre) = _
  unfold EVM.binaryMachineStateOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, hpop]
  rfl

/-- **One `RETURN` opcode.** Pops the offset and the length and publishes the
padded read into `H_return`. -/
theorem step_RETURN (fuel gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256)
    (hpop : pre.stack.pop2 = some (s, μ₀, μ₁)) :
    StepOk (fuel + 1) gasCost (.RETURN, none) pre
      (EVM.State.replaceStackAndIncrPC
        { stepPre gasCost pre with
            toMachineState := (stepPre gasCost pre).toMachineState.evmReturn μ₀ μ₁ } s) := by
  show EvmYul.step (τ := .EVM) .RETURN none (stepPre gasCost pre) = _
  show EVM.binaryMachineStateOp MachineState.evmReturn (stepPre gasCost pre) = _
  unfold EVM.binaryMachineStateOp
  rw [show (stepPre gasCost pre).stack = pre.stack from rfl, hpop]
  rfl

/-! ## What `MSTORE` leaves behind

Abbreviations for the post-states, so the corollaries do not have to repeat the
record updates. -/

/-- The post-state of the `MSTORE` in `step_MSTORE`. -/
abbrev mstorePost (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256) : State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre gasCost pre with
        toMachineState := (stepPre gasCost pre).toMachineState.mstore μ₀ μ₁ } s

/-- The post-state of the `RETURN` in `step_RETURN`. -/
abbrev returnPost (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256) : State :=
  EVM.State.replaceStackAndIncrPC
    { stepPre gasCost pre with
        toMachineState := (stepPre gasCost pre).toMachineState.evmReturn μ₀ μ₁ } s

/-- Charging gas and counting the instruction does not touch memory, so the
memory an opcode sees is the memory of `pre`. -/
@[simp] theorem memory_stepPre (gasCost : ℕ) (pre : State) :
    (stepPre gasCost pre).memory = pre.memory := rfl

/-- **The real `MSTORE` opcode does charge `M`.** This is the `activeWords` side
of the store, and it is *all* the expansion charge amounts to. -/
theorem activeWords_step_MSTORE (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256) :
    (mstorePost gasCost pre s μ₀ μ₁).activeWords
      = UInt256.ofNat (MachineState.M pre.activeWords.toNat μ₀.toNat 32) := rfl

/-- **…and the charge is not where the in-bounds fact comes from.** Memory after
the opcode is exactly what `ByteArray.write` produced; the `activeWords` update
contributes nothing to it. Compare `MachineState.memory_activeWords_update`. -/
theorem memory_step_MSTORE_eq (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256) :
    (mstorePost gasCost pre s μ₀ μ₁).memory
      = (pre.toMachineState.mstore μ₀ μ₁).memory := rfl

/-- **How far the real `MSTORE` opcode grows memory.** -/
theorem size_memory_step_MSTORE (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256)
    (hpad : μ₀.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (mstorePost gasCost pre s μ₀ μ₁).memory.size = max pre.memory.size (μ₀.toNat + 32) := by
  rw [memory_step_MSTORE_eq]
  exact MachineState.size_memory_mstore_of_pad pre.toMachineState μ₀ μ₁ hpad

/-- **The in-bounds fact, at the opcode layer.** After a real `MSTORE` the stored
span is inside memory — no hypothesis about memory beforehand, and in particular
no appeal to charged expansion. This is the replacement for the unprovable
`μ₀.toNat + 32 ≤ pre.memory.size`. -/
theorem le_size_memory_step_MSTORE (gasCost : ℕ) (pre : State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) (hpad : μ₀.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    μ₀.toNat + 32 ≤ (mstorePost gasCost pre s μ₀ μ₁).memory.size := by
  rw [size_memory_step_MSTORE gasCost pre s μ₀ μ₁ hpad]
  omega

/-- The same, for a store starting at or before the current end of memory, where
the `hpad` parameter discharges automatically. Fresh frames (`memory.size = 0`,
`μ₀ = 0`) are the main instance. -/
theorem le_size_memory_step_MSTORE_of_le (gasCost : ℕ) (pre : State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) (hstart : μ₀.toNat ≤ pre.memory.size) :
    μ₀.toNat + 32 ≤ (mstorePost gasCost pre s μ₀ μ₁).memory.size :=
  le_size_memory_step_MSTORE gasCost pre s μ₀ μ₁
    (by rw [show μ₀.toNat - pre.memory.size = 0 from by omega]; positivity)

/-- **Reading back the word a real `MSTORE` opcode stored.** -/
theorem readWithPadding_memory_step_MSTORE (gasCost : ℕ) (pre : State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) (hstart : μ₀.toNat ≤ pre.memory.size) :
    (mstorePost gasCost pre s μ₀ μ₁).memory.readWithPadding μ₀.toNat 32 = μ₁.toByteArray := by
  rw [memory_step_MSTORE_eq]
  exact MachineState.readWithPadding_memory_mstore_of_le pre.toMachineState μ₀ μ₁ hstart

/-! ## What `RETURN` publishes -/

/-- **`RETURN` publishes a padded read of the memory it was handed.** -/
theorem H_return_step_RETURN (gasCost : ℕ) (pre : State) (s : Stack UInt256) (μ₀ μ₁ : UInt256) :
    (returnPost gasCost pre s μ₀ μ₁).H_return
      = pre.memory.readWithPadding μ₀.toNat μ₁.toNat := rfl

/-- **`RETURN` of a span whose contents are already known.** The form a caller
uses after establishing what memory holds — for instance by
`readWithPadding_memory_step_MSTORE`, possibly across intervening instructions
that leave memory alone (`Z_ok_memory`). -/
theorem H_return_step_RETURN_of_read (gasCost : ℕ) (pre : State) (s : Stack UInt256)
    (μ₀ μ₁ : UInt256) (o : ByteArray)
    (hread : pre.memory.readWithPadding μ₀.toNat μ₁.toNat = o) :
    (returnPost gasCost pre s μ₀ μ₁).H_return = o := by
  rw [H_return_step_RETURN]; exact hread

/-! ## The canonical residual

`MSTORE` immediately followed by `RETURN` of the same span. This is the shape an
`EndpointAgrees`-style correspondence proof is left with once the `CfgState` side
— which has no memory at all — has been discharged. -/

/-- **`MSTORE` then `RETURN`, as two real opcode steps.** The bytes the fragment
returns are the word that was stored. Only `hstart` is assumed about memory, and
for a store at the current end of memory it is free. -/
theorem H_return_step_MSTORE_RETURN (f₁ g₁ f₂ g₂ : ℕ) (pre : State)
    (s s' : Stack UInt256) (μ₀ μ₁ len : UInt256)
    (hpop : pre.stack.pop2 = some (s, μ₀, μ₁))
    (hpop' : s.pop2 = some (s', μ₀, len))
    (hlen : len.toNat = 32)
    (hstart : μ₀.toNat ≤ pre.memory.size) :
    ∃ post, Runs [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.RETURN, none))] pre post
      ∧ post.H_return = μ₁.toByteArray := by
  refine ⟨returnPost g₂ (mstorePost g₁ pre s μ₀ μ₁) s' μ₀ len,
    .cons (step_MSTORE f₁ g₁ pre s μ₀ μ₁ hpop)
      (.one (step_RETURN f₂ g₂ (mstorePost g₁ pre s μ₀ μ₁) s' μ₀ len ?_)), ?_⟩
  · exact hpop'
  · rw [H_return_step_RETURN, hlen]
    exact readWithPadding_memory_step_MSTORE g₁ pre s μ₀ μ₁ hstart

/-- **The canonical fragment, no hypothesis about memory.** `MSTORE(0, v)` then
`RETURN(0, 32)` returns `v`, from *any* starting state — in particular from a
fresh frame, where `memory.size = 0` and where charged expansion would have been
no help. -/
theorem H_return_step_MSTORE_RETURN_zero (f₁ g₁ f₂ g₂ : ℕ) (pre : State)
    (s s' : Stack UInt256) (sval len : UInt256)
    (hpop : pre.stack.pop2 = some (s, ⟨0⟩, sval))
    (hpop' : s.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 32) :
    ∃ post, Runs [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.RETURN, none))] pre post
      ∧ post.H_return = sval.toByteArray :=
  H_return_step_MSTORE_RETURN f₁ g₁ f₂ g₂ pre s s' ⟨0⟩ sval len hpop hpop' hlen
    (by show (0 : ℕ) ≤ _; exact Nat.zero_le _)

/-- **The canonical fragment with the returned word opened up.** Same run as
`H_return_step_MSTORE_RETURN_zero`, but the conclusion names the 32 base-256
digits of `sval` instead of the opaque `sval.toByteArray`. A correspondence proof
whose abstract side publishes a big-endian encoding matches against this one. -/
theorem H_return_step_MSTORE_RETURN_zero_digits (f₁ g₁ f₂ g₂ : ℕ) (pre : State)
    (s s' : Stack UInt256) (sval len : UInt256)
    (hpop : pre.stack.pop2 = some (s, ⟨0⟩, sval))
    (hpop' : s.pop2 = some (s', ⟨0⟩, len))
    (hlen : len.toNat = 32) :
    ∃ post, Runs [(f₁ + 1, g₁, (.MSTORE, none)), (f₂ + 1, g₂, (.RETURN, none))] pre post
      ∧ post.H_return.size = 32
      ∧ (List.range post.H_return.size).map (fun i => (post.H_return.get! i).toNat)
          = (List.range 32).map (fun i => sval.toNat / 256 ^ (32 - 1 - i) % 256) := by
  obtain ⟨post, hruns, hret⟩ :=
    H_return_step_MSTORE_RETURN_zero f₁ g₁ f₂ g₂ pre s s' sval len hpop hpop' hlen
  refine ⟨post, hruns, ?_, ?_⟩
  · rw [hret]; exact UInt256.size_toByteArray sval
  · rw [hret]; exact UInt256.map_toNat_get!_toByteArray sval

end EvmYul.EVM.Proof
