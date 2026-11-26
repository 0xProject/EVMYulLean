import EvmYul.EVM.Proof.Execution

/-! # Running to a stop condition, and basic blocks

`EvmYul.EVM.Proof.Execution` peels `X` one instruction at a time. Neither it nor
the raw semantics can yet talk about a *block*: a maximal straight-line stretch
of code, which is the unit a correspondence proof actually wants to reason
about.

This file supplies that layer.

* `Halting` classifies the instructions after which `X` stops, and proves the
  classification is a property of the opcode alone — `H` reads the machine state
  only to fetch the returned bytes, never to decide whether to stop.
* `Z_ok_state` is the frame theorem for `X`'s exceptional-halting check: when `Z`
  accepts, the state it hands to `step` is the pre-state with the memory
  expansion charged and *nothing else touched*. This is what lets a block-level
  statement be phrased against the state `X` decoded the instruction in, instead
  of against `Z`'s otherwise invisible output.
* `RunUntil` composes consecutive non-halting iterations of `X` until a named
  stop condition fires or the fuel is spent, and `xRunUntil` is the executable
  driver, validated against it in both directions.
* `XReaches` is the trace-erased form the block tactics work in, and `x_step` /
  `x_block` discharge a short straight-line block from step facts in the
  context.

Everything here rests on `EvmYul.EVM.Proof.Execution` alone. No axiom is
introduced and no proof is admitted.
-/

namespace EvmYul.EVM.Proof

open EvmYul EvmYul.EVM

/-! ## Halting is a property of the opcode

`X` consults `H` after every instruction to decide whether to stop. `H` takes a
machine state, but only ever to read `H_return` out of it on the branch that has
already decided to halt. `Halting` is the same decision without the machine
state, and `H_eq_none_iff` is the proof that nothing was lost. -/

/-- The instructions after which `X` stops. The two-part shape mirrors `H`'s two
nested tests so that the equivalence below is a case split and not a search. -/
def Halting (w : Operation .EVM) : Bool :=
  w ∈ [Operation.RETURN, .REVERT] || w ∈ [Operation.STOP, .SELFDESTRUCT]

/-- `H`'s machine-state argument does not influence whether `X` halts. -/
theorem H_eq_none_iff {μ : MachineState} {w : Operation .EVM} :
    H μ w = none ↔ Halting w = false := by
  simp only [H, Halting, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  split
  · rename_i h; simp [h]
  · split <;> rename_i h₁ h₂ <;> simp [h₁, h₂]

theorem H_eq_none_of_not_halting {μ : MachineState} {w : Operation .EVM}
    (h : Halting w = false) : H μ w = none :=
  H_eq_none_iff.mpr h

theorem halting_of_H_eq_some {μ : MachineState} {w : Operation .EVM} {o : ByteArray}
    (h : H μ w = some o) : Halting w = true := by
  rcases hw : Halting w with _ | _
  · exact absurd (h ▸ H_eq_none_of_not_halting (μ := μ) hw) (by simp)
  · rfl

/-- The converse: at a halting opcode `H` really does produce output bytes, in
every machine state. This is what lets a block-level halting lemma be stated
from `Halting` alone, without the caller first naming the returned data. -/
theorem H_eq_some_of_halting {μ : MachineState} {w : Operation .EVM}
    (h : Halting w = true) : ∃ o, H μ w = some o := by
  cases hH : H μ w with
  | none => rw [H_eq_none_iff.mp hH] at h; simp at h
  | some o => exact ⟨o, rfl⟩

@[simp] theorem halting_RETURN : Halting .RETURN = true := by decide
@[simp] theorem halting_REVERT : Halting .REVERT = true := by decide
@[simp] theorem halting_STOP : Halting .STOP = true := by decide
@[simp] theorem halting_SELFDESTRUCT : Halting .SELFDESTRUCT = true := by decide
@[simp] theorem halting_JUMPDEST : Halting .JUMPDEST = false := by decide
@[simp] theorem halting_JUMP : Halting .JUMP = false := by decide
@[simp] theorem halting_JUMPI : Halting .JUMPI = false := by decide
@[simp] theorem halting_SSTORE : Halting .SSTORE = false := by decide
@[simp] theorem halting_MSTORE : Halting .MSTORE = false := by decide
@[simp] theorem halting_MSTORE8 : Halting .MSTORE8 = false := by decide
@[simp] theorem halting_LOG0 : Halting .LOG0 = false := by decide
@[simp] theorem halting_LOG1 : Halting .LOG1 = false := by decide
@[simp] theorem halting_LOG2 : Halting .LOG2 = false := by decide
@[simp] theorem halting_LOG3 : Halting .LOG3 = false := by decide
@[simp] theorem halting_LOG4 : Halting .LOG4 = false := by decide

/-! ## Named stop conditions

A stop condition is a predicate on the decoded opcode. `CallFamily` and
`BlockEnd` name the two that a correspondence proof asks for; any other
predicate works just as well, since nothing below inspects these definitions. -/

/-- The instructions that re-enter `X` on a child state. A block cannot be
continued through one of these without a statement about the callee. -/
def CallFamily (w : Operation .EVM) : Bool := w.isCall || w.isCreate

/-- The end of a basic block: a halt, a call, or any transfer of control.
`JUMPDEST` is included because it is where control can *arrive*, so a block that
ran through one would not be maximal. -/
def BlockEnd (w : Operation .EVM) : Bool :=
  Halting w || CallFamily w || w ∈ [Operation.JUMP, .JUMPI, .JUMPDEST]

/-- A stop condition, widened so that it also fires on every halting
instruction. `X` stops there whether or not the caller asked it to, so a runner
that did not stop would be describing a continuation that does not exist. -/
def stopOrHalting (stop : Operation .EVM → Bool) (w : Operation .EVM) : Bool :=
  stop w || Halting w

@[simp] theorem stopOrHalting_of_halting {stop : Operation .EVM → Bool} {w : Operation .EVM}
    (h : Halting w = true) : stopOrHalting stop w = true := by
  simp [stopOrHalting, h]

theorem stopOrHalting_of_stop {stop : Operation .EVM → Bool} {w : Operation .EVM}
    (h : stop w = true) : stopOrHalting stop w = true := by
  simp [stopOrHalting, h]

theorem stopOrHalting_eq_false {stop : Operation .EVM → Bool} {w : Operation .EVM}
    (h : stopOrHalting stop w = false) : stop w = false ∧ Halting w = false := by
  simpa [stopOrHalting] using h

/-- `BlockEnd` already stops at every halt, so widening it changes nothing. -/
@[simp] theorem stopOrHalting_blockEnd : stopOrHalting BlockEnd = BlockEnd := by
  funext w
  simp only [stopOrHalting, BlockEnd]
  cases Halting w <;> simp

/-! ## `Z` is a gas frame

`Z` is `X`'s exceptional-halting check. It is written as a long chain of guards
around a single state update, and the update is the memory-expansion charge. So
whenever `Z` accepts, everything a block-level statement wants to observe —
storage, memory, logs, the stack, the program counter — is unchanged.

Without this theorem every block lemma would have to be phrased against `Z`'s
output, which is a state no caller can name. -/

/-- The state `Z` hands to `step` once it has accepted: the pre-state with this
instruction's memory expansion charged. Naming it is what lets every lemma below
be phrased against `pre` alone. -/
def zMid (pre : State) (w : Operation .EVM) : State :=
  { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (memoryExpansionCost pre w) }

/-- A guard in `Z` that did not fire may be dropped. `Z`'s body is a chain of
these, so peeling with this lemma walks the chain one guard at a time. `simp`
cannot do it: `Z`'s unfolded body is large enough to exhaust the simp step
budget, and `split_ifs` re-elaborates every branch. -/
theorem elim_guard {α ε : Type} {c : Prop} [Decidable c] {e : ε}
    {rest : Except ε α} {v : α} (h : (if c then Except.error e else rest) = Except.ok v) :
    rest = Except.ok v := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact absurd h (by simp)
  · rwa [ite_eq_right hc] at h

/-- The same peel, keeping the information that the guard did not fire. -/
theorem elim_guard_not {α ε : Type} {c : Prop} [Decidable c] {e : ε}
    {rest : Except ε α} {v : α} (h : (if c then Except.error e else rest) = Except.ok v) : ¬ c := by
  intro hc
  rw [ite_eq_left hc] at h
  exact absurd h (by simp)

/-- **The frame theorem for `Z`.** An accepted instruction is charged for memory
expansion and nothing else moves. -/
theorem Z_ok_state {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) : mid = zMid pre w := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at h
  repeat replace h := elim_guard h
  exact (congrArg Prod.fst (Except.ok.inj h)).symm

/-- `Z` rejects an instruction the stack is too shallow for, so an accepted one
has all its arguments. This is what lets a step lemma destructure the stack
without the caller having to supply its depth. -/
theorem Z_ok_stack_length {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    (δ w).getD 0 ≤ pre.stack.length := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at h
  replace h := elim_guard h
  replace h := elim_guard h
  replace h := elim_guard h
  exact Nat.le_of_not_lt (elim_guard_not h)

@[simp] theorem Z_ok_toState {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.toState = pre.toState := by rw [Z_ok_state h]; rfl

theorem Z_ok_stack {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.stack = pre.stack := by rw [Z_ok_state h]; rfl

theorem Z_ok_memory {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.memory = pre.memory := by rw [Z_ok_state h]; rfl

theorem Z_ok_executionEnv {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.executionEnv = pre.executionEnv := by rw [Z_ok_state h]; rfl

theorem Z_ok_substate {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.substate = pre.substate := by rw [Z_ok_state h]; rfl

theorem Z_ok_accountMap {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.accountMap = pre.accountMap := by rw [Z_ok_state h]; rfl

theorem Z_ok_pc {validJumps : Array UInt256} {w : Operation .EVM} {pre mid : State}
    {gasCost : ℕ} (h : Z validJumps w pre = .ok (mid, gasCost)) :
    mid.pc = pre.pc := by rw [Z_ok_state h]; rfl

@[simp] theorem zMid_stack (pre : State) (w : Operation .EVM) : (zMid pre w).stack = pre.stack := rfl
@[simp] theorem zMid_toState (pre : State) (w : Operation .EVM) :
    (zMid pre w).toState = pre.toState := rfl
@[simp] theorem zMid_memory (pre : State) (w : Operation .EVM) :
    (zMid pre w).memory = pre.memory := rfl
@[simp] theorem zMid_executionEnv (pre : State) (w : Operation .EVM) :
    (zMid pre w).executionEnv = pre.executionEnv := rfl
@[simp] theorem zMid_substate (pre : State) (w : Operation .EVM) :
    (zMid pre w).substate = pre.substate := rfl
@[simp] theorem zMid_accountMap (pre : State) (w : Operation .EVM) :
    (zMid pre w).accountMap = pre.accountMap := rfl

/-! ## Inverting a step

A block-level proof needs to go from "a step happened" to "here is where it
landed". `XStepAt.post_eq_of_step` is that inversion, and it is generic — the
caller supplies the step equation for the opcode at hand and gets the post-state
pinned, with `Z`'s output already eliminated by `Z_ok_state`. -/

/-- `step` has no fuel-free case, so a step that succeeded had fuel to spend.
This is what lets an inversion use `fuel + 1` step equations at a fuel that is
only a variable. -/
theorem StepOk.fuel_pos {fuel gasCost : ℕ} {instr : Instruction} {pre post : State}
    (h : StepOk fuel gasCost instr pre post) : ∃ f, fuel = f + 1 := by
  cases fuel with
  | zero =>
      have h' : (Except.error .OutOfFuel : Except EVM.ExecutionException State) = .ok post := h
      simp at h'
  | succ f => exact ⟨f, rfl⟩

theorem XStepAt.fuel_pos {validJumps : Array UInt256} {fuel gasCost : ℕ} {pre post : State}
    (h : XStepAt validJumps fuel gasCost pre post) : ∃ f, fuel = f + 1 := by
  obtain ⟨_, -, hstep, -⟩ := h
  exact StepOk.fuel_pos hstep

/-- **Step inversion.** `Z`'s output is always `zMid`, so knowing what `step`
does to `zMid` is knowing where the step landed. -/
theorem XStepAt.post_eq_of_step {validJumps : Array UInt256} {fuel gasCost : ℕ}
    {pre post target : State} (h : XStepAt validJumps fuel gasCost pre post)
    (hstep : EvmYul.EVM.step fuel gasCost (some (decodeAt pre)) (zMid pre (decodeAt pre).1)
      = .ok target) : post = target := by
  obtain ⟨mid, hZ, hs, -⟩ := h
  rw [Z_ok_state hZ] at hs
  have hs' : EvmYul.EVM.step fuel gasCost (some (decodeAt pre)) (zMid pre (decodeAt pre).1)
      = .ok post := hs
  exact Except.ok.inj (hs'.symm.trans hstep)

/-- A step never runs a halting instruction: `X` would have stopped instead. -/
theorem XStepAt.not_halting {validJumps : Array UInt256} {fuel gasCost : ℕ} {pre post : State}
    (h : XStepAt validJumps fuel gasCost pre post) : Halting (decodeAt pre).1 = false := by
  obtain ⟨_, -, -, hH⟩ := h
  exact H_eq_none_iff.mp hH

/-- Knowing the opcode `X` decoded is knowing the decode, since the argument is
whatever the decode returned. -/
theorem decodeAt_eq_of_fst {pre : State} {w : Operation .EVM} (h : (decodeAt pre).1 = w) :
    decodeAt pre = (w, (decodeAt pre).2) := by rw [← h]

/-! ## Running to a stop condition

`XRuns` chains non-halting iterations of `X`, but says nothing about *why* the
chain ended: any prefix of a run is a run. `RunUntil` closes that gap. It ends
only for a reason it records — the decoded opcode satisfies the stop condition,
or the fuel is gone — so `RunUntil.stopped` can hand a correspondence proof the
fact that the continuation begins at a block boundary.

The trace is still an index, so everything `XRuns` proves about fuel accounting
carries over through `RunUntil.toXRuns`. -/

/-- `X` runs from `pre` to `post`, taking only instructions that neither halt nor
satisfy `stop`, and ending as soon as one does — or when the fuel runs out. -/
inductive RunUntil (stop : Operation .EVM → Bool) (validJumps : Array UInt256) :
    ℕ → State → List Labelled → ℕ → State → Prop
  | stop {fuel : ℕ} {state : State} (h : stopOrHalting stop (decodeAt state).1 = true) :
      RunUntil stop validJumps fuel state [] fuel state
  | out_of_fuel (state : State) : RunUntil stop validJumps 0 state [] 0 state
  | step {fuel gasCost rem : ℕ} {pre mid post : State} {trace : List Labelled}
      (hgo : stopOrHalting stop (decodeAt pre).1 = false)
      (hstep : XStepAt validJumps fuel gasCost pre mid)
      (tail : RunUntil stop validJumps fuel mid trace rem post) :
      RunUntil stop validJumps (fuel + 1) pre ((fuel, gasCost, decodeAt pre) :: trace) rem post

/-- A `RunUntil` is an `XRuns`: it is the same chain of steps, with a reason for
stopping attached. Everything `XRuns` proves therefore applies. -/
theorem RunUntil.toXRuns {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) :
    XRuns validJumps fuel pre trace rem post := by
  induction h with
  | stop => exact .refl _ _
  | out_of_fuel state => exact .refl _ _
  | step _ hstep _ ih => exact .cons hstep ih

/-- **The composition theorem.** A block may be replaced by its endpoints: `X`
from the entry state is `X` from the exit state at the fuel the block left. -/
theorem RunUntil.X_eq {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) :
    X fuel validJumps pre = X rem validJumps post :=
  h.toXRuns.X_eq

/-- `X` spends one unit of fuel per instruction of the block. -/
theorem RunUntil.length {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) : trace.length + rem = fuel :=
  h.toXRuns.length

theorem RunUntil.rem_le {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) : rem ≤ fuel :=
  h.toXRuns.rem_le

/-- **The reason the block ended.** Either the fuel is gone, or the exit state
decodes to an instruction the caller asked to stop at. This is the fact that
makes `RunUntil` more than a prefix of a run. -/
theorem RunUntil.stopped {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) :
    rem = 0 ∨ stopOrHalting stop (decodeAt post).1 = true := by
  induction h with
  | stop h => exact Or.inr h
  | out_of_fuel => exact Or.inl rfl
  | step _ _ _ ih => exact ih

/-- A block that ended with fuel to spare ended at a stop instruction. -/
theorem RunUntil.stop_of_rem_pos {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) (hrem : rem ≠ 0) :
    stopOrHalting stop (decodeAt post).1 = true :=
  h.stopped.resolve_left hrem

/-- A block that ran its fuel out leaves `X` out of fuel. -/
theorem RunUntil.X_outOfFuel {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace 0 post) :
    X fuel validJumps pre = .error .OutOfFuel := h.toXRuns.X_outOfFuel

/-- A block is determined by its entry state and its fuel: the stop condition
decides where it ends, and each step is a function. So `RunUntil` is a partial
function, not merely a relation, and a proof may not silently pick a different
exit state. -/
theorem RunUntil.deterministic {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem₁ rem₂ : ℕ} {trace₁ trace₂ : List Labelled} {pre post₁ post₂ : State}
    (h₁ : RunUntil stop validJumps fuel pre trace₁ rem₁ post₁)
    (h₂ : RunUntil stop validJumps fuel pre trace₂ rem₂ post₂) :
    trace₁ = trace₂ ∧ rem₁ = rem₂ ∧ post₁ = post₂ := by
  induction h₁ generalizing trace₂ rem₂ post₂ with
  | stop hs =>
      cases h₂ with
      | stop => exact ⟨rfl, rfl, rfl⟩
      | out_of_fuel => exact ⟨rfl, rfl, rfl⟩
      | step hgo => exact absurd hs (by rw [hgo]; simp)
  | out_of_fuel state =>
      cases h₂ with
      | stop => exact ⟨rfl, rfl, rfl⟩
      | out_of_fuel => exact ⟨rfl, rfl, rfl⟩
  | step hgo hstep _ ih =>
      cases h₂ with
      | stop hs => exact absurd hs (by rw [hgo]; simp)
      | step _ hstep' tail' =>
          obtain ⟨rfl, rfl⟩ := XStepAt.deterministic hstep hstep'
          obtain ⟨rfl, rfl, rfl⟩ := ih tail'
          exact ⟨rfl, rfl, rfl⟩

/-! ### What a block does to `X`

Composing `RunUntil.X_eq` with the one-step decomposition of
`EvmYul.EVM.Proof.Execution` turns a whole straight-line block plus its
terminating instruction into `X`'s answer. These are the shapes a `Ξ`
correspondence consumes: the block is gone, and only its endpoints remain. -/

/-- A block that runs into a normal halt fixes `X`'s result outright. -/
theorem RunUntil.X_success {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem gasCost : ℕ} {trace : List Labelled} {pre exit mid post : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {o : ByteArray}
    (hrun : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w ≠ .REVERT) :
    X fuel validJumps pre = .ok (.success post o) := by
  rw [hrun.X_eq]
  exact X_succ_of_halt hdec hZ hstep hH hw

/-- A block that runs into a `REVERT` fixes `X`'s result outright. -/
theorem RunUntil.X_revert {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem gasCost : ℕ} {trace : List Labelled} {pre exit mid post : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {o : ByteArray}
    (hrun : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w = .REVERT) :
    X fuel validJumps pre = .ok (.revert post.gasAvailable o) := by
  rw [hrun.X_eq]
  exact X_succ_of_revert hdec hZ hstep hH hw

/-- A block followed by any non-`REVERT` halt returns *some* output, without the
caller having to say which bytes. `Halting` is enough because `H` produces
output at every halting opcode. -/
theorem RunUntil.X_success_of_halting {stop : Operation .EVM → Bool}
    {validJumps : Array UInt256} {fuel rem gasCost : ℕ} {trace : List Labelled}
    {pre exit mid post : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hrun : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hhalt : Halting w = true)
    (hw : w ≠ .REVERT) :
    ∃ o, X fuel validJumps pre = .ok (.success post o) := by
  obtain ⟨o, ho⟩ := H_eq_some_of_halting (μ := post.toMachineState) hhalt
  exact ⟨o, hrun.X_success hdec hZ hstep ho hw⟩

/-- A block whose terminating instruction `Z` rejects makes `X` halt
exceptionally. -/
theorem RunUntil.X_Z_error {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre exit : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {e : EVM.ExecutionException}
    (hrun : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .error e) :
    X fuel validJumps pre = .error e := by
  rw [hrun.X_eq]
  exact X_succ_of_Z_error hdec hZ

/-- A block whose terminating instruction itself fails makes `X` propagate the
failure. -/
theorem RunUntil.X_step_error {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem gasCost : ℕ} {trace : List Labelled} {pre exit mid : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {e : EVM.ExecutionException}
    (hrun : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hdec : decodeAt exit = (w, arg))
    (hZ : Z validJumps w exit = .ok (mid, gasCost))
    (hstep : Step rem gasCost (w, arg) mid (.error e)) :
    X fuel validJumps pre = .error e := by
  rw [hrun.X_eq]
  exact X_succ_of_step_error hdec hZ hstep

/-! ## The executable driver

`RunUntil` is a relation, so nothing about it can be *computed*. `xRunUntil`
walks the same block and returns the trace it took. It is validated in both
directions: `xRunUntil_sound` says its answer is a `RunUntil`, and
`xRunUntil_complete` says it finds every `RunUntil` there is. A caller may
therefore discharge a concrete block by evaluation and still hold a proof.

The driver never inspects a post-state to decide whether to continue, which is
exactly what `Halting` being a property of the opcode buys: the decision is made
before the instruction runs, and `H_eq_none_of_not_halting` supplies the
non-halting side condition afterwards. -/

/-- Walk a block: run non-halting, non-stopping instructions until the stop
condition fires or the fuel is spent, returning the trace, the fuel left, and
the exit state. -/
def xRunUntil (stop : Operation .EVM → Bool) (validJumps : Array UInt256) :
    ℕ → State → Except EVM.ExecutionException (List Labelled × ℕ × State)
  | 0, state => .ok ([], 0, state)
  | fuel + 1, state =>
      if stopOrHalting stop (decodeAt state).1 then
        .ok ([], fuel + 1, state)
      else
        match Z validJumps (decodeAt state).1 state with
        | .error e => .error e
        | .ok zres =>
            match EvmYul.EVM.step fuel zres.2 (some (decodeAt state)) zres.1 with
            | .error e => .error e
            | .ok post =>
                match xRunUntil stop validJumps fuel post with
                | .error e => .error e
                | .ok res => .ok ((fuel, zres.2, decodeAt state) :: res.1, res.2)

/-- **The driver is sound.** Anything `xRunUntil` computes is a `RunUntil`, so
evaluating it on a concrete block yields a theorem about `X`. -/
theorem xRunUntil_sound {stop : Operation .EVM → Bool} {validJumps : Array UInt256} :
    ∀ {fuel : ℕ} {pre : State} {trace : List Labelled} {rem : ℕ} {post : State},
      xRunUntil stop validJumps fuel pre = .ok (trace, rem, post) →
      RunUntil stop validJumps fuel pre trace rem post := by
  intro fuel
  induction fuel with
  | zero =>
      intro pre trace rem post h
      simp only [xRunUntil, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .out_of_fuel pre
  | succ f ih =>
      intro pre trace rem post h
      rw [xRunUntil] at h
      split at h
      · rename_i hstop
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .stop hstop
      · rename_i hgo
        replace hgo : stopOrHalting stop (decodeAt pre).1 = false := by
          simpa using hgo
        split at h
        · exact absurd h (by simp)
        · rename_i zres hZ
          split at h
          · exact absurd h (by simp)
          · rename_i post' hs
            split at h
            · exact absurd h (by simp)
            · rename_i res hrec
              obtain ⟨rtrace, rrem, rpost⟩ := res
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              refine .step hgo ⟨zres.1, hZ, hs, ?_⟩ (ih hrec)
              exact H_eq_none_of_not_halting (stopOrHalting_eq_false hgo).2

/-- **The driver is complete.** Every `RunUntil` is found by `xRunUntil`, so the
relation adds no blocks the driver would miss. With soundness this makes
`xRunUntil` a decision procedure for `RunUntil`, and `RunUntil.deterministic` a
corollary rather than a coincidence. -/
theorem xRunUntil_complete {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) :
    xRunUntil stop validJumps fuel pre = .ok (trace, rem, post) := by
  induction h with
  | @stop fuel state hstop =>
      cases fuel with
      | zero => rfl
      | succ f => rw [xRunUntil, ite_eq_left hstop]
  | out_of_fuel state => rfl
  | @step fuel gasCost rem pre mid post trace hgo hstep _ ih =>
      obtain ⟨zmid, hZ, hs, -⟩ := hstep
      have hs' : EvmYul.EVM.step fuel gasCost (some (decodeAt pre)) zmid = .ok mid := hs
      rw [xRunUntil, ite_eq_right (by simp [hgo])]
      simp only [hZ, hs', ih]

/-! ## Trace-erased runs

A straight-line block is usually reasoned about without naming the trace: what
matters is that `X` gets from here to there, and how much fuel it spent.
`XReaches` is `XRuns` with the trace existentially quantified. It is the form the
tactics below work in, because it has no index a tactic would have to invent. -/

/-- `X` gets from `pre` to `post` without halting, spending `fuel - rem` fuel. -/
def XReaches (validJumps : Array UInt256) (fuel : ℕ) (pre : State) (rem : ℕ) (post : State) : Prop :=
  ∃ trace, XRuns validJumps fuel pre trace rem post

theorem XReaches.refl (validJumps : Array UInt256) (fuel : ℕ) (state : State) :
    XReaches validJumps fuel state fuel state := ⟨[], .refl _ _⟩

/-- Prepend one non-halting iteration of `X`. This is the shape `x_step` refines
against, which is why the step comes first. -/
theorem XReaches.head {validJumps : Array UInt256} {fuel gasCost rem : ℕ} {pre mid post : State}
    (hstep : XStepAt validJumps fuel gasCost pre mid)
    (tail : XReaches validJumps fuel mid rem post) :
    XReaches validJumps (fuel + 1) pre rem post := by
  obtain ⟨trace, htail⟩ := tail
  exact ⟨_, .cons hstep htail⟩

theorem XReaches.of_stepAt {validJumps : Array UInt256} {fuel gasCost : ℕ} {pre post : State}
    (h : XStepAt validJumps fuel gasCost pre post) :
    XReaches validJumps (fuel + 1) pre fuel post :=
  .head h (.refl _ _ _)

theorem XReaches.trans {validJumps : Array UInt256} {f g r : ℕ} {s₀ s₁ s₂ : State}
    (h₁ : XReaches validJumps f s₀ g s₁) (h₂ : XReaches validJumps g s₁ r s₂) :
    XReaches validJumps f s₀ r s₂ := by
  obtain ⟨t₁, h₁⟩ := h₁
  obtain ⟨t₂, h₂⟩ := h₂
  exact ⟨_, h₁.trans h₂⟩

/-- **Composition, trace-erased.** The whole point: a block may be replaced by
its endpoints. -/
theorem XReaches.X_eq {validJumps : Array UInt256} {fuel rem : ℕ} {pre post : State}
    (h : XReaches validJumps fuel pre rem post) :
    X fuel validJumps pre = X rem validJumps post := by
  obtain ⟨trace, h⟩ := h
  exact h.X_eq

theorem XReaches.rem_le {validJumps : Array UInt256} {fuel rem : ℕ} {pre post : State}
    (h : XReaches validJumps fuel pre rem post) : rem ≤ fuel := by
  obtain ⟨trace, h⟩ := h
  exact h.rem_le

/-- `XReaches` is a partial function too, inherited from `XStep`. -/
theorem XReaches.deterministic_of_eq_rem {validJumps : Array UInt256} {fuel rem : ℕ}
    {pre post₁ post₂ : State}
    (h₁ : XReaches validJumps fuel pre rem post₁) (h₂ : XReaches validJumps fuel pre rem post₂) :
    X rem validJumps post₁ = X rem validJumps post₂ := by
  rw [← h₁.X_eq, ← h₂.X_eq]

theorem RunUntil.toXReaches {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem : ℕ} {trace : List Labelled} {pre post : State}
    (h : RunUntil stop validJumps fuel pre trace rem post) :
    XReaches validJumps fuel pre rem post := ⟨trace, h.toXRuns⟩

/-! ### Chaining blocks across a boundary

A `RunUntil` cannot be extended: it has already stopped. What a control-flow
proof actually chains is *block, boundary instruction, next block*. At the
trace-erased level that composition is available, and it is the statement that
lets a whole path through a control-flow graph collapse to its endpoints. -/

/-- Run a block, take the boundary instruction it stopped at, then run the next
block: the result reaches the far end. -/
theorem RunUntil.trans_step {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem rem' gasCost : ℕ} {trace trace' : List Labelled} {pre exit next post : State}
    (h₁ : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hcross : XStepAt validJumps rem gasCost exit next)
    (h₂ : RunUntil stop validJumps rem next trace' rem' post) :
    XReaches validJumps fuel pre rem' post :=
  h₁.toXReaches.trans (XReaches.head hcross h₂.toXReaches)

/-- The same chain, stated where it is used: `X` from the entry of the first
block is `X` from the exit of the second. -/
theorem RunUntil.X_eq_trans_step {stop : Operation .EVM → Bool} {validJumps : Array UInt256}
    {fuel rem rem' gasCost : ℕ} {trace trace' : List Labelled} {pre exit next post : State}
    (h₁ : RunUntil stop validJumps fuel pre trace (rem + 1) exit)
    (hcross : XStepAt validJumps rem gasCost exit next)
    (h₂ : RunUntil stop validJumps rem next trace' rem' post) :
    X fuel validJumps pre = X rem' validJumps post :=
  (h₁.trans_step hcross h₂).X_eq

/-! ## Automation

`x_step` peels one instruction off an `XReaches` goal by finding the matching
`XStepAt` fact in the context; `x_block` peels the whole block and closes with
reflexivity. Between them a short straight-line stretch is discharged without
the caller naming a single intermediate state. `x_collapse` carries that through
to an `X` goal, replacing the entry state by the exit state.

The gas cost and the intermediate state are left as named holes rather than
inferred, because at the moment a step is peeled neither is yet determined: both
are fixed by the hypothesis `assumption` finds.

The tactics are deliberately small: they search the local context and nothing
else, so they cannot silently invent a step that was never proved. -/

/-- Peel one non-halting `X` step off an `XReaches` goal, taking the step from a
hypothesis. Fails when no hypothesis matches, which is what lets `x_block` stop. -/
macro "x_step" : tactic =>
  `(tactic| (refine XReaches.head (gasCost := ?gas) (mid := ?mid) ?step ?rest
             case step => assumption))

/-- Discharge a straight-line block: peel steps while the context supplies them,
then close by reflexivity. -/
macro "x_block" : tactic =>
  `(tactic| ((repeat x_step); exact XReaches.refl ..))

/-- Replace the entry state of an `X` goal by the exit state of a straight-line
block discharged from the context, leaving the remaining goal to the caller. -/
macro "x_collapse" : tactic =>
  `(tactic| (refine Eq.trans (XReaches.X_eq (rem := ?rem) (post := ?post) ?blk) ?after
             case blk => x_block))

/-! ## Non-vacuity

`RunUntil`, `XReaches` and the tactics are all exercised below on real steps, so
none of the theorems above is proved about an empty relation. `JUMPDEST` is the
cheapest instruction `X` continues through, and `EvmYul.EVM.Proof.Execution`
already supplies its step, so these witnesses do not depend on evaluating a
concrete machine state. -/

/-- `JUMPDEST` is not a call, so a `CallFamily` block runs through it. -/
@[simp] theorem stopOrHalting_callFamily_JUMPDEST :
    stopOrHalting CallFamily .JUMPDEST = false := by decide

/-- `XReaches` is inhabited beyond `refl`: one payable `JUMPDEST` reaches. -/
theorem xReaches_one_JUMPDEST {validJumps : Array UInt256} {fuel : ℕ} {pre : State}
    (hdec : decodeAt pre = (.JUMPDEST, none))
    (hgas : GasConstants.Gjumpdest ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (hstack : pre.stack.length ≤ 1024) :
    XReaches validJumps (fuel + 2) pre (fuel + 1)
      (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC :=
  .of_stepAt (xStepAt_JUMPDEST hdec hgas hstack)

/-- `RunUntil` is inhabited beyond its two stopping cases: a `JUMPDEST` that the
state can pay for is one step of a `CallFamily` block, and the block then ends
wherever the caller says it does. -/
theorem runUntil_one_JUMPDEST {validJumps : Array UInt256} {fuel : ℕ} {pre : State}
    (hdec : decodeAt pre = (.JUMPDEST, none))
    (hgas : GasConstants.Gjumpdest ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (hstack : pre.stack.length ≤ 1024)
    (hstop : stopOrHalting CallFamily
      (decodeAt (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC).1 = true) :
    RunUntil CallFamily validJumps (fuel + 2) pre
      [(fuel + 1, GasConstants.Gjumpdest, (.JUMPDEST, none))] (fuel + 1)
      (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC := by
  have hgo : stopOrHalting CallFamily (decodeAt pre).1 = false := by
    rw [hdec]; exact stopOrHalting_callFamily_JUMPDEST
  have hstep : XStepAt validJumps (fuel + 1) GasConstants.Gjumpdest pre
      (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC :=
    xStepAt_JUMPDEST hdec hgas hstack
  have h := RunUntil.step (stop := CallFamily) hgo hstep (.stop hstop)
  rwa [hdec] at h

/-- The tactics are exercised, not merely defined: `x_block` chains two steps
from the context without either intermediate state being named in the proof. -/
theorem xReaches_two_steps {validJumps : Array UInt256} {fuel g₁ g₂ : ℕ} {s₀ s₁ s₂ : State}
    (h₁ : XStepAt validJumps (fuel + 1) g₁ s₀ s₁)
    (h₂ : XStepAt validJumps fuel g₂ s₁ s₂) :
    XReaches validJumps (fuel + 2) s₀ fuel s₂ := by
  x_block

/-- Three steps, to confirm that `x_block` iterates rather than unfolding a fixed
depth. -/
theorem xReaches_three_steps {validJumps : Array UInt256} {fuel g₁ g₂ g₃ : ℕ}
    {s₀ s₁ s₂ s₃ : State}
    (h₁ : XStepAt validJumps (fuel + 2) g₁ s₀ s₁)
    (h₂ : XStepAt validJumps (fuel + 1) g₂ s₁ s₂)
    (h₃ : XStepAt validJumps fuel g₃ s₂ s₃) :
    XReaches validJumps (fuel + 3) s₀ fuel s₃ := by
  x_block

/-- `x_collapse` moves an `X` goal across a block discharged from the context. -/
theorem X_eq_of_two_steps {validJumps : Array UInt256} {fuel g₁ g₂ : ℕ} {s₀ s₁ s₂ : State}
    (h₁ : XStepAt validJumps (fuel + 1) g₁ s₀ s₁)
    (h₂ : XStepAt validJumps fuel g₂ s₁ s₂) :
    X (fuel + 2) validJumps s₀ = X fuel validJumps s₂ := by
  x_collapse
  rfl

end EvmYul.EVM.Proof
