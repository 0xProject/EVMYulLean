import EvmYul.EVM.Semantics

namespace EvmYul.EVM.Proof

open EvmYul EvmYul.EVM

/-! ## The raw one-step relation

`EvmYul.EVM.step` is the executable single-instruction transition.  `Step` is its
graph.  The result is kept as an `Except`, so exceptional executions are recorded
rather than being given an invented post-state.
-/

/-- A decoded EVM instruction together with its optional `PUSH` argument. -/
abbrev Instruction := Operation .EVM × Option (UInt256 × Nat)

/-- The graph of the executable `EvmYul.EVM.step`. -/
def Step (fuel gasCost : Nat) (instr : Instruction) (pre : State)
    (result : Except EVM.ExecutionException State) : Prop :=
  EvmYul.EVM.step fuel gasCost (some instr) pre = result

/-- The successful-state projection of `Step`. -/
abbrev StepOk (fuel gasCost : Nat) (instr : Instruction) (pre post : State) : Prop :=
  Step fuel gasCost instr pre (.ok post)

theorem Step.deterministic {fuel gasCost : Nat} {instr : Instruction} {pre : State}
    {r₁ r₂ : Except EVM.ExecutionException State}
    (h₁ : Step fuel gasCost instr pre r₁) (h₂ : Step fuel gasCost instr pre r₂) : r₁ = r₂ := by
  rw [← h₁, ← h₂]

theorem Step.deterministic_ok {fuel gasCost : Nat} {instr : Instruction} {pre post₁ post₂ : State}
    (h₁ : StepOk fuel gasCost instr pre post₁) (h₂ : StepOk fuel gasCost instr pre post₂) :
    post₁ = post₂ :=
  Except.ok.inj (Step.deterministic h₁ h₂)

/-! ## Multi-step runs

Each entry of the trace carries its own `fuel` and `gasCost`.  This is forced by
`X`: it decrements fuel on every iteration and recomputes the gas cost per
instruction through `C'`, so a run labelled by a single shared `gasCost` could not
describe any real code execution. -/

/-- One trace entry: the fuel, the gas cost, and the decoded instruction. -/
abbrev Labelled := Nat × Nat × Instruction

/-- A successful run through a fixed labelled trace. -/
inductive Runs : List Labelled → State → State → Prop
  | nil (state : State) : Runs [] state state
  | cons {fuel gasCost : Nat} {instr : Instruction} {pre mid post : State} {rest : List Labelled}
      (step : StepOk fuel gasCost instr pre mid) (tail : Runs rest mid post) :
      Runs ((fuel, gasCost, instr) :: rest) pre post

@[simp] theorem Runs.nil_iff {pre post : State} : Runs [] pre post ↔ pre = post := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .nil _

theorem Runs.one {fuel gasCost : Nat} {instr : Instruction} {pre post : State}
    (h : StepOk fuel gasCost instr pre post) : Runs [(fuel, gasCost, instr)] pre post :=
  .cons h (.nil post)

@[simp] theorem Runs.cons_iff {fuel gasCost : Nat} {instr : Instruction}
    {rest : List Labelled} {pre post : State} :
    Runs ((fuel, gasCost, instr) :: rest) pre post ↔
      ∃ mid, StepOk fuel gasCost instr pre mid ∧ Runs rest mid post := by
  constructor
  · intro h; cases h with | cons hstep htail => exact ⟨_, hstep, htail⟩
  · rintro ⟨mid, hstep, htail⟩; exact .cons hstep htail

theorem Runs.trans {xs ys : List Labelled} {s₀ s₁ s₂ : State}
    (h₁ : Runs xs s₀ s₁) (h₂ : Runs ys s₁ s₂) : Runs (xs ++ ys) s₀ s₂ := by
  induction h₁ with
  | nil => simpa using h₂
  | cons step _ ih => exact .cons step (ih h₂)

theorem Runs.deterministic {xs : List Labelled} {pre post₁ post₂ : State}
    (h₁ : Runs xs pre post₁) (h₂ : Runs xs pre post₂) : post₁ = post₂ := by
  induction h₁ generalizing post₂ with
  | nil => exact Runs.nil_iff.mp h₂
  | cons step _ ih =>
      obtain ⟨mid, step', tail'⟩ := Runs.cons_iff.mp h₂
      exact ih (Step.deterministic_ok step step' ▸ tail')

/-- Execute a fixed labelled trace. -/
def runN : List Labelled → State → Except EVM.ExecutionException State
  | [], state => .ok state
  | (fuel, gasCost, instr) :: rest, state => do
      let state' ← EvmYul.EVM.step fuel gasCost (some instr) state
      runN rest state'

theorem runN_sound {trace : List Labelled} {pre post : State}
    (h : runN trace pre = .ok post) : Runs trace pre post := by
  induction trace generalizing pre with
  | nil =>
      simp only [runN, Except.ok.injEq] at h
      subst post
      exact .nil pre
  | cons entry rest ih =>
      obtain ⟨fuel, gasCost, instr⟩ := entry
      simp only [runN] at h
      cases hstep : EvmYul.EVM.step fuel gasCost (some instr) pre with
      | error e => rw [hstep] at h; simp only [Bind.bind, Except.bind] at h; exact absurd h (by simp)
      | ok mid => rw [hstep] at h; simp only [Bind.bind, Except.bind] at h; exact .cons hstep (ih h)

theorem runN_complete {trace : List Labelled} {pre post : State}
    (h : Runs trace pre post) : runN trace pre = .ok post := by
  induction h with
  | nil => rfl
  | @cons fuel gasCost instr pre mid post rest step _ ih =>
      have hs : EvmYul.EVM.step fuel gasCost (some instr) pre = .ok mid := step
      simp only [runN, hs, Bind.bind, Except.bind]
      exact ih

theorem runN_iff_runs {trace : List Labelled} {pre post : State} :
    runN trace pre = .ok post ↔ Runs trace pre post :=
  ⟨runN_sound, runN_complete⟩

/-! ## The internals of `X`, exposed

`X` inlines its static-mode predicate `W`, its exceptional-halting check `Z` and
its halting-data function `H` as local definitions, so no proof outside `X` can
refer to them.  The following definitions mirror them verbatim.  They are not
assumed to agree with `X`: the mirrors are *validated* by the decomposition
theorems below, each of which unfolds `X` and rewrites with the mirror.  A drift
between a mirror and `X` breaks those proofs rather than passing silently. -/

/-- Mirror of the static-mode predicate `W` inlined in `X` (YP (159)). -/
def W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
  w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
  (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)

/-- Mirror of the exceptional-halting check `Z` inlined in `X` (YP (158)). -/
def Z (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) := do
  let cost₁ := memoryExpansionCost evmState w
  if evmState.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := evmState.gasAvailable - .ofNat cost₁
  let evmState := { evmState with gasAvailable := gasAvailable}
  let cost₂ := C' evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  if δ w = none then
    .error .InvalidInstruction

  if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow

  let invalidJump := X.notIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  then
    .error .OutOfGass

  pure (evmState, cost₂)

/-- Mirror of the halting-data function `H` inlined in `X`. -/
def H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
  if w ∈ [.RETURN, .REVERT] then
    some <| μ.H_return
  else
    if w ∈ [.STOP, .SELFDESTRUCT] then
      some .empty
    else none

/-- The instruction `X` decodes at the current `pc`, with `X`'s `STOP` default. -/
def decodeAt (evmState : State) : Instruction :=
  (decode evmState.toState.executionEnv.code evmState.pc).getD (.STOP, .none)

/-! ## One-step decomposition of `X`

`X` is the iterative progression of `step`.  The six theorems below are a
complete case analysis of a single iteration: out of fuel, an exceptional halt
detected by `Z`, a failing `step`, a non-halting continuation, a normal halt, and
a `REVERT` halt.  Together they let a proof peel `X` one instruction at a time
without ever re-deriving `X`'s body. -/

@[simp] theorem X_zero (validJumps : Array UInt256) (evmState : State) :
    X 0 validJumps evmState = .error .OutOfFuel := by
  rw [X.eq_def]

/-- `Z` rejects the instruction: `X` halts exceptionally. -/
theorem X_succ_of_Z_error {fuel : ℕ} {validJumps : Array UInt256} {pre : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {e : EVM.ExecutionException}
    (hdec : decodeAt pre = (w, arg))
    (hZ : Z validJumps w pre = .error e) :
    X (fuel + 1) validJumps pre = .error e := by
  rw [X.eq_def]
  simp only [decodeAt] at hdec
  simp only [hdec]
  simp only [Z, W] at hZ
  rw [hZ]

/-- `Z` accepts but the instruction itself fails: `X` propagates the failure. -/
theorem X_succ_of_step_error {fuel : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {gasCost : ℕ}
    {e : EVM.ExecutionException}
    (hdec : decodeAt pre = (w, arg))
    (hZ : Z validJumps w pre = .ok (mid, gasCost))
    (hstep : Step fuel gasCost (w, arg) mid (.error e)) :
    X (fuel + 1) validJumps pre = .error e := by
  have hs : EvmYul.EVM.step fuel gasCost (some (w, arg)) mid = .error e := hstep
  rw [X.eq_def]
  simp only [decodeAt] at hdec
  simp only [hdec]
  simp only [Z, W] at hZ
  rw [hZ]
  simp only [hs, Bind.bind, Except.bind]

/-- The instruction does not halt: one iteration of `X` is one `step`, and the
remaining computation is `X` at one less fuel.  This is the key decomposition. -/
theorem X_succ_of_continue {fuel : ℕ} {validJumps : Array UInt256} {pre mid post : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {gasCost : ℕ}
    (hdec : decodeAt pre = (w, arg))
    (hZ : Z validJumps w pre = .ok (mid, gasCost))
    (hstep : StepOk fuel gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = none) :
    X (fuel + 1) validJumps pre = X fuel validJumps post := by
  have hs : EvmYul.EVM.step fuel gasCost (some (w, arg)) mid = .ok post := hstep
  rw [X.eq_def]
  simp only [decodeAt] at hdec
  simp only [hdec]
  simp only [Z, W] at hZ
  rw [hZ]
  simp only [hs, Bind.bind, Except.bind]
  simp only [H] at hH
  rw [hH]

/-- The instruction halts normally: `X` returns a success with its output. -/
theorem X_succ_of_halt {fuel : ℕ} {validJumps : Array UInt256} {pre mid post : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {gasCost : ℕ} {o : ByteArray}
    (hdec : decodeAt pre = (w, arg))
    (hZ : Z validJumps w pre = .ok (mid, gasCost))
    (hstep : StepOk fuel gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w ≠ .REVERT) :
    X (fuel + 1) validJumps pre = .ok (.success post o) := by
  have hs : EvmYul.EVM.step fuel gasCost (some (w, arg)) mid = .ok post := hstep
  rw [X.eq_def]
  simp only [decodeAt] at hdec
  simp only [hdec]
  simp only [Z, W] at hZ
  rw [hZ]
  simp only [hs, Bind.bind, Except.bind]
  simp only [H] at hH
  rw [hH]
  simp only [beq_iff_eq, hw, ite_false]

/-- The instruction is `REVERT`: `X` returns a revert carrying the remaining gas. -/
theorem X_succ_of_revert {fuel : ℕ} {validJumps : Array UInt256} {pre mid post : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {gasCost : ℕ} {o : ByteArray}
    (hdec : decodeAt pre = (w, arg))
    (hZ : Z validJumps w pre = .ok (mid, gasCost))
    (hstep : StepOk fuel gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w = .REVERT) :
    X (fuel + 1) validJumps pre = .ok (.revert post.gasAvailable o) := by
  have hs : EvmYul.EVM.step fuel gasCost (some (w, arg)) mid = .ok post := hstep
  rw [X.eq_def]
  simp only [decodeAt] at hdec
  simp only [hdec]
  simp only [Z, W] at hZ
  rw [hZ]
  simp only [hs, Bind.bind, Except.bind]
  simp only [H] at hH
  rw [hH]
  simp only [beq_iff_eq, hw, ite_true]

/-! ## `X`-level runs

`XStep` is the non-halting iteration of `X`, and `XRuns` chains it.  Both track
the fuel explicitly, because `X` decrements fuel on every iteration and passes it
to `step` (where it bounds `CALL`/`CREATE` recursion). -/

/-- One non-halting iteration of `X` at fuel `fuel + 1`, charging `gasCost`. -/
def XStepAt (validJumps : Array UInt256) (fuel gasCost : ℕ) (pre post : State) : Prop :=
  ∃ mid,
    Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost) ∧
    StepOk fuel gasCost (decodeAt pre) mid post ∧
    H post.toMachineState (decodeAt pre).1 = none

/-- One non-halting iteration of `X` at fuel `fuel + 1`, from `pre` to `post`. -/
def XStep (validJumps : Array UInt256) (fuel : ℕ) (pre post : State) : Prop :=
  ∃ gasCost, XStepAt validJumps fuel gasCost pre post

theorem XStepAt.X_succ {validJumps : Array UInt256} {fuel gasCost : ℕ} {pre post : State}
    (h : XStepAt validJumps fuel gasCost pre post) :
    X (fuel + 1) validJumps pre = X fuel validJumps post := by
  obtain ⟨mid, hZ, hstep, hH⟩ := h
  exact X_succ_of_continue rfl hZ hstep hH

theorem XStep.X_succ {validJumps : Array UInt256} {fuel : ℕ} {pre post : State}
    (h : XStep validJumps fuel pre post) :
    X (fuel + 1) validJumps pre = X fuel validJumps post := by
  obtain ⟨_, h⟩ := h
  exact h.X_succ

/-- `Z` is a function, so an `XStep` fixes both the gas it charges and its
post-state. -/
theorem XStepAt.deterministic {validJumps : Array UInt256} {fuel gas₁ gas₂ : ℕ}
    {pre post₁ post₂ : State}
    (h₁ : XStepAt validJumps fuel gas₁ pre post₁) (h₂ : XStepAt validJumps fuel gas₂ pre post₂) :
    gas₁ = gas₂ ∧ post₁ = post₂ := by
  obtain ⟨mid₁, hZ₁, hstep₁, -⟩ := h₁
  obtain ⟨mid₂, hZ₂, hstep₂, -⟩ := h₂
  rw [hZ₁] at hZ₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Except.ok.inj hZ₂
  exact ⟨rfl, Step.deterministic_ok hstep₁ hstep₂⟩

theorem XStep.deterministic {validJumps : Array UInt256} {fuel : ℕ} {pre post₁ post₂ : State}
    (h₁ : XStep validJumps fuel pre post₁) (h₂ : XStep validJumps fuel pre post₂) :
    post₁ = post₂ := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  exact (XStepAt.deterministic h₁ h₂).2

/-- `XStep` factors through the raw step relation: `Z` produces the gas cost, and
the instruction is then run by `EvmYul.EVM.step`. -/
theorem XStepAt.toRuns {validJumps : Array UInt256} {fuel gasCost : ℕ} {pre post : State}
    (h : XStepAt validJumps fuel gasCost pre post) :
    ∃ mid, Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost) ∧
      Runs [(fuel, gasCost, decodeAt pre)] mid post := by
  obtain ⟨mid, hZ, hstep, -⟩ := h
  exact ⟨mid, hZ, .one hstep⟩

/-- `X` runs from `pre` at fuel `fuel` down to `post` at fuel `rem`, never halting,
executing exactly `trace`.

The trace is an index rather than an existential, so a run *carries* the
instructions it took, each with the fuel and the gas cost `X` used for it. That
is what makes the fuel accounting in `XRuns.length` a statement about this run
rather than about some list of the right length. -/
inductive XRuns (validJumps : Array UInt256) : ℕ → State → List Labelled → ℕ → State → Prop
  | refl (fuel : ℕ) (state : State) : XRuns validJumps fuel state [] fuel state
  | cons {fuel gasCost rem : ℕ} {pre mid post : State} {trace : List Labelled}
      (step : XStepAt validJumps fuel gasCost pre mid)
      (tail : XRuns validJumps fuel mid trace rem post) :
      XRuns validJumps (fuel + 1) pre ((fuel, gasCost, decodeAt pre) :: trace) rem post

/-- The decomposition theorem: a non-halting `X`-run may be replaced by its tail. -/
theorem XRuns.X_eq {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre post : State} (h : XRuns validJumps fuel pre trace rem post) :
    X fuel validJumps pre = X rem validJumps post := by
  induction h with
  | refl => rfl
  | cons step _ ih => exact (step.X_succ).trans ih

/-- `X` spends exactly one unit of fuel per instruction it executes. -/
theorem XRuns.length {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre post : State} (h : XRuns validJumps fuel pre trace rem post) :
    trace.length + rem = fuel := by
  induction h with
  | refl => simp
  | cons _ _ ih => simp only [List.length_cons]; omega

theorem XRuns.rem_le {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre post : State} (h : XRuns validJumps fuel pre trace rem post) : rem ≤ fuel :=
  h.length ▸ Nat.le_add_left _ _

theorem XRuns.trans {validJumps : Array UInt256} {f g r : ℕ} {xs ys : List Labelled}
    {s₀ s₁ s₂ : State}
    (h₁ : XRuns validJumps f s₀ xs g s₁) (h₂ : XRuns validJumps g s₁ ys r s₂) :
    XRuns validJumps f s₀ (xs ++ ys) r s₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | cons step _ ih => exact .cons step (ih h₂)

/-- Each trace entry is a genuine `XStepAt` of this run, and the entry's fuel is
the fuel `X` had left when it reached that instruction. -/
theorem XRuns.head_step {validJumps : Array UInt256} {fuel gasCost rem : ℕ}
    {instr : Instruction} {trace : List Labelled} {pre post : State}
    (h : XRuns validJumps fuel pre ((fuel - 1, gasCost, instr) :: trace) rem post) :
    ∃ mid, XStepAt validJumps (fuel - 1) gasCost pre mid ∧
      instr = decodeAt pre ∧ XRuns validJumps (fuel - 1) mid trace rem post := by
  cases h with
  | cons step tail => exact ⟨_, step, rfl, tail⟩

/-- An `X`-run that exhausts its fuel without halting runs out of fuel. -/
theorem XRuns.X_outOfFuel {validJumps : Array UInt256} {fuel : ℕ} {trace : List Labelled}
    {pre post : State} (h : XRuns validJumps fuel pre trace 0 post) :
    X fuel validJumps pre = .error .OutOfFuel := by
  rw [h.X_eq, X_zero]

/-- An `X`-run followed by a normal halt determines `X`'s result. -/
theorem XRuns.X_success {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre halting mid post : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {gasCost : ℕ} {o : ByteArray}
    (hrun : XRuns validJumps fuel pre trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z validJumps w halting = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w ≠ .REVERT) :
    X fuel validJumps pre = .ok (.success post o) := by
  rw [hrun.X_eq]
  exact X_succ_of_halt hdec hZ hstep hH hw

/-! ## Non-vacuity

`Step`, `Runs`, `XStepAt` and `XRuns` are all inhabited beyond their reflexive
cases, so none of the theorems above is proved about an empty relation.

`JUMPDEST` is the cheapest instruction that `X` continues through: it only pays
gas and advances the program counter.  Its step is computed symbolically, for an
arbitrary pre-state, so these witnesses do not depend on evaluating a concrete
machine state. -/

/-- The state `EVM.step` hands to an opcode implementation: one more instruction
counted, and this instruction's gas already deducted. -/
def stepPre (gasCost : ℕ) (pre : State) : State :=
  { pre with execLength := pre.execLength + 1,
             gasAvailable := pre.gasAvailable - UInt256.ofNat gasCost }

theorem step_JUMPDEST (fuel gasCost : ℕ) (pre : State) :
    StepOk (fuel + 1) gasCost (.JUMPDEST, none) pre (stepPre gasCost pre).incrPC := by
  rfl

@[simp] theorem H_JUMPDEST (μ : MachineState) : H μ .JUMPDEST = none := by
  rfl

/-- `Z` accepts `JUMPDEST` whenever the state can pay for it and the stack is not
already full.  `JUMPDEST` touches no memory, so it expands none and its whole
cost is `Gjumpdest`. -/
theorem Z_JUMPDEST (validJumps : Array UInt256) (pre : State)
    (hgas : GasConstants.Gjumpdest ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (hstack : pre.stack.length ≤ 1024) :
    Z validJumps .JUMPDEST pre
      = .ok ({pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0},
             GasConstants.Gjumpdest) := by
  simp only [GasConstants.Gjumpdest] at hgas
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, C',
    GasConstants.Gjumpdest]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [δ, α, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [hstack]

/-- `XStepAt` is inhabited: every `JUMPDEST` that `X` can pay for is one
non-halting iteration of `X`. -/
theorem xStepAt_JUMPDEST {validJumps : Array UInt256} {fuel : ℕ} {pre : State}
    (hdec : decodeAt pre = (.JUMPDEST, none))
    (hgas : GasConstants.Gjumpdest ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (hstack : pre.stack.length ≤ 1024) :
    XStepAt validJumps (fuel + 1) GasConstants.Gjumpdest pre
      (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC := by
  refine ⟨{ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, ?_, ?_, ?_⟩
  · simp only [hdec]; exact Z_JUMPDEST validJumps pre hgas hstack
  · simp only [hdec]; exact step_JUMPDEST ..
  · simp only [hdec]; exact H_JUMPDEST _

/-- `XRuns` is inhabited beyond `refl`, so the `X`-level API is not vacuous. -/
theorem xRuns_one_JUMPDEST {validJumps : Array UInt256} {fuel : ℕ} {pre : State}
    (hdec : decodeAt pre = (.JUMPDEST, none))
    (hgas : GasConstants.Gjumpdest ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (hstack : pre.stack.length ≤ 1024) :
    XRuns validJumps (fuel + 2) pre [(fuel + 1, GasConstants.Gjumpdest, (.JUMPDEST, none))]
      (fuel + 1)
      (stepPre GasConstants.Gjumpdest
        { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }).incrPC := by
  have h := XRuns.cons (xStepAt_JUMPDEST (validJumps := validJumps) hdec hgas hstack)
    (.refl (fuel + 1) _)
  rwa [hdec] at h

/-- `Runs` is inhabited at every pre-state: two `JUMPDEST`s advance the counter twice. -/
theorem runs_two_JUMPDEST (fuel gasCost : ℕ) (pre : State) :
    Runs [(fuel + 1, gasCost, (.JUMPDEST, none)), (fuel + 1, gasCost, (.JUMPDEST, none))] pre
      (stepPre gasCost (stepPre gasCost pre).incrPC).incrPC :=
  .cons (step_JUMPDEST ..) (.one (step_JUMPDEST ..))

end EvmYul.EVM.Proof
