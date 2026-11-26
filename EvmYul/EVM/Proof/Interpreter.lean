import EvmYul.EVM.Proof.Execution

/-!
# Decomposition of `X` and `Ξ` into runs

`EvmYul.EVM.Proof.Execution` exposes one iteration of `X` as six cases and chains
the non-halting ones into `XRuns`.  Those six theorems are *sufficient*
conditions: each says that if such-and-such holds then `X` does such-and-such.
This module closes the development in the two directions that leaves open.

* **The cases are exhaustive.** `X_succ_complete` shows every `X (fuel + 1)` is
  one of them, so a case split on `XOneStep` is a complete case split on `X`.

* **Every `X` is a maximal run plus one terminal event.** `X_decompose` extracts
  from an arbitrary `X` an `XRuns` prefix ending in a configuration that takes no
  further non-halting iteration, and `XStuck.X_terminal` shows such a
  configuration is out of fuel, raises, or halts — the `progress` case is ruled
  out rather than merely not chosen.

* **`Ξ` is `X` on a fresh state.** `Ξ_succ_eq` states that equation, so every
  `X`-level result above transports to the transaction-level interpreter.
-/

namespace EvmYul.EVM.Proof

open EvmYul EvmYul.EVM

/-! ## Halting and exceptional endings of an `X`-run

`XRuns.X_success` covers a run that ends in a normal halt.  The other three
endings complete the picture: a `REVERT`, an exceptional halt detected by `Z`,
and an instruction whose own execution fails. -/

/-- An `X`-run followed by a `REVERT` determines `X`'s result. -/
theorem XRuns.X_revert {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre halting mid post : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {gasCost : ℕ} {o : ByteArray}
    (hrun : XRuns validJumps fuel pre trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z validJumps w halting = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid post)
    (hH : H post.toMachineState w = some o)
    (hw : w = .REVERT) :
    X fuel validJumps pre = .ok (.revert post.gasAvailable o) := by
  rw [hrun.X_eq]
  exact X_succ_of_revert hdec hZ hstep hH hw

/-- An `X`-run that reaches an instruction `Z` rejects raises that exception. -/
theorem XRuns.X_exception {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre halting : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {e : EVM.ExecutionException}
    (hrun : XRuns validJumps fuel pre trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z validJumps w halting = .error e) :
    X fuel validJumps pre = .error e := by
  rw [hrun.X_eq]
  exact X_succ_of_Z_error hdec hZ

/-- An `X`-run that reaches an instruction whose execution fails propagates that
failure. -/
theorem XRuns.X_stepError {validJumps : Array UInt256} {fuel rem : ℕ} {trace : List Labelled}
    {pre halting mid : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {gasCost : ℕ} {e : EVM.ExecutionException}
    (hrun : XRuns validJumps fuel pre trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z validJumps w halting = .ok (mid, gasCost))
    (hstep : Step rem gasCost (w, arg) mid (.error e)) :
    X fuel validJumps pre = .error e := by
  rw [hrun.X_eq]
  exact X_succ_of_step_error hdec hZ hstep

/-! ## The one-step case analysis is a partition

`XOneStep` packages the five ways a single iteration of `X` at positive fuel can
go.  Each constructor carries the side conditions *and* the resulting value of
`X`, so `cases` on it both splits the execution and supplies the equation for
that branch. -/

/-- The complete case analysis of one iteration of `X` at fuel `fuel + 1`. -/
inductive XOneStep (validJumps : Array UInt256) (fuel : ℕ) (pre : State) : Prop
  /-- `Z` rejects the instruction. -/
  | exception (e : EVM.ExecutionException)
      (hZ : Z validJumps (decodeAt pre).1 pre = .error e)
      (hX : X (fuel + 1) validJumps pre = .error e)
  /-- `Z` accepts but the instruction itself fails. -/
  | stepError (mid : State) (gasCost : ℕ) (e : EVM.ExecutionException)
      (hZ : Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost))
      (hstep : Step fuel gasCost (decodeAt pre) mid (.error e))
      (hX : X (fuel + 1) validJumps pre = .error e)
  /-- The instruction does not halt, so `X` continues at one less fuel. -/
  | progress (mid post : State) (gasCost : ℕ)
      (hZ : Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost))
      (hstep : StepOk fuel gasCost (decodeAt pre) mid post)
      (hH : H post.toMachineState (decodeAt pre).1 = none)
      (hX : X (fuel + 1) validJumps pre = X fuel validJumps post)
  /-- The instruction halts normally. -/
  | halt (mid post : State) (gasCost : ℕ) (o : ByteArray)
      (hZ : Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost))
      (hstep : StepOk fuel gasCost (decodeAt pre) mid post)
      (hH : H post.toMachineState (decodeAt pre).1 = some o)
      (hw : (decodeAt pre).1 ≠ .REVERT)
      (hX : X (fuel + 1) validJumps pre = .ok (.success post o))
  /-- The instruction is `REVERT`. -/
  | revert (mid post : State) (gasCost : ℕ) (o : ByteArray)
      (hZ : Z validJumps (decodeAt pre).1 pre = .ok (mid, gasCost))
      (hstep : StepOk fuel gasCost (decodeAt pre) mid post)
      (hH : H post.toMachineState (decodeAt pre).1 = some o)
      (hw : (decodeAt pre).1 = .REVERT)
      (hX : X (fuel + 1) validJumps pre = .ok (.revert post.gasAvailable o))

/-- Every iteration of `X` at positive fuel falls into exactly one of the five
cases, so the decomposition theorems of `Execution` are complete and not merely
sound. -/
theorem X_succ_complete (validJumps : Array UInt256) (fuel : ℕ) (pre : State) :
    XOneStep validJumps fuel pre := by
  cases hZ : Z validJumps (decodeAt pre).1 pre with
  | error e => exact .exception e hZ (X_succ_of_Z_error rfl hZ)
  | ok zres =>
      obtain ⟨mid, gasCost⟩ := zres
      cases hstep : EvmYul.EVM.step fuel gasCost (some (decodeAt pre)) mid with
      | error e =>
          exact .stepError mid gasCost e hZ hstep (X_succ_of_step_error rfl hZ hstep)
      | ok post =>
          cases hH : H post.toMachineState (decodeAt pre).1 with
          | none =>
              exact .progress mid post gasCost hZ hstep hH (X_succ_of_continue rfl hZ hstep hH)
          | some o =>
              by_cases hw : (decodeAt pre).1 = .REVERT
              · exact .revert mid post gasCost o hZ hstep hH hw
                  (X_succ_of_revert rfl hZ hstep hH hw)
              · exact .halt mid post gasCost o hZ hstep hH hw
                  (X_succ_of_halt rfl hZ hstep hH hw)

/-! ## Maximal runs

An `XRuns` records only non-halting iterations, so a run may stop early for no
reason.  `XStuck` names the configurations where it *cannot* be extended, and
`X_decompose` shows every `X` reaches one. -/

/-- At fuel `rem` from `post`, `X` takes no further non-halting iteration: either
the fuel is gone, or the next instruction halts or raises. -/
def XStuck (validJumps : Array UInt256) (rem : ℕ) (post : State) : Prop :=
  ∀ fuel', rem = fuel' + 1 → ∀ next, ¬ XStep validJumps fuel' post next

theorem XStuck.zero (validJumps : Array UInt256) (post : State) : XStuck validJumps 0 post := by
  intro fuel' h
  exact absurd h (by omega)

/-- **Every `X` execution is a maximal run followed by a stuck configuration.**
The run carries the instructions it executed, each with the fuel and gas `X`
spent on it, and `X`'s result is the result at the configuration it stops in. -/
theorem X_decompose (validJumps : Array UInt256) (fuel : ℕ) (pre : State) :
    ∃ (trace : List Labelled) (rem : ℕ) (post : State),
      XRuns validJumps fuel pre trace rem post ∧
      X fuel validJumps pre = X rem validJumps post ∧
      XStuck validJumps rem post := by
  induction fuel generalizing pre with
  | zero => exact ⟨[], 0, pre, .refl 0 pre, rfl, XStuck.zero validJumps pre⟩
  | succ f ih =>
      by_cases hnext : ∃ next, XStep validJumps f pre next
      · obtain ⟨next, gasCost, hstep⟩ := hnext
        obtain ⟨trace, rem, post, hrun, heq, hstuck⟩ := ih next
        exact ⟨_, rem, post, .cons hstep hrun, (XStepAt.X_succ hstep).trans heq, hstuck⟩
      · refine ⟨[], f + 1, pre, .refl (f + 1) pre, rfl, ?_⟩
        intro fuel' h next hstep
        have hf : fuel' = f := by omega
        subst hf
        exact hnext ⟨next, hstep⟩

/-- A stuck configuration really does stop: its `X` is decided by fuel
exhaustion, by an exception, or by one halting instruction.  The `progress` case
of `X_succ_complete` is impossible here, which is what makes `X_decompose`'s run
maximal. -/
theorem XStuck.X_terminal {validJumps : Array UInt256} {rem : ℕ} {post : State}
    (h : XStuck validJumps rem post) :
    (rem = 0 ∧ X rem validJumps post = .error .OutOfFuel) ∨
    (∃ e, Z validJumps (decodeAt post).1 post = .error e ∧
      X rem validJumps post = .error e) ∨
    (∃ mid gasCost e, Z validJumps (decodeAt post).1 post = .ok (mid, gasCost) ∧
      Step (rem - 1) gasCost (decodeAt post) mid (.error e) ∧
      X rem validJumps post = .error e) ∨
    (∃ mid gasCost final o, Z validJumps (decodeAt post).1 post = .ok (mid, gasCost) ∧
      StepOk (rem - 1) gasCost (decodeAt post) mid final ∧
      H final.toMachineState (decodeAt post).1 = some o ∧
      X rem validJumps post =
        .ok (if (decodeAt post).1 = .REVERT then .revert final.gasAvailable o
             else .success final o)) := by
  cases rem with
  | zero => exact .inl ⟨rfl, X_zero validJumps post⟩
  | succ f =>
      simp only [Nat.add_sub_cancel]
      cases X_succ_complete validJumps f post with
      | exception e hZ hX => exact .inr (.inl ⟨e, hZ, hX⟩)
      | stepError mid gasCost e hZ hstep hX =>
          exact .inr (.inr (.inl ⟨mid, gasCost, e, hZ, hstep, hX⟩))
      | progress mid next gasCost hZ hstep hH _ =>
          exact absurd ⟨gasCost, mid, hZ, hstep, hH⟩ (h f rfl next)
      | halt mid final gasCost o hZ hstep hH hw hX =>
          exact .inr (.inr (.inr ⟨mid, gasCost, final, o, hZ, hstep, hH, by rw [hX, ite_eq_right hw]⟩))
      | revert mid final gasCost o hZ hstep hH hw hX =>
          exact .inr (.inr (.inr ⟨mid, gasCost, final, o, hZ, hstep, hH, by rw [hX, ite_eq_left hw]⟩))

/-- `X`'s fuel is spent entirely on the instructions of its maximal run and on
whatever the terminal configuration has left. -/
theorem X_runs_terminal (validJumps : Array UInt256) (fuel : ℕ) (pre : State) :
    ∃ (trace : List Labelled) (rem : ℕ) (post : State),
      XRuns validJumps fuel pre trace rem post ∧
      trace.length + rem = fuel ∧
      X fuel validJumps pre = X rem validJumps post ∧
      XStuck validJumps rem post := by
  obtain ⟨trace, rem, post, hrun, heq, hstuck⟩ := X_decompose validJumps fuel pre
  exact ⟨trace, rem, post, hrun, hrun.length, heq, hstuck⟩

/-! ## The transaction-level interpreter `Ξ`

`Ξ` builds a fresh machine state from the account map, substate and execution
environment it is given, computes the jump-destination table of the code, and
hands both to `X`.  The three mirrors below name those three pieces, and
`Ξ_succ_eq` validates them by proving the equation they are supposed to satisfy;
a drift breaks that proof rather than passing silently. -/

/-- Mirror of the fresh machine state `Ξ` builds before entering `X`. -/
def xiState (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) : State :=
  { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-- Mirror of the jump-destination table `Ξ` computes for the code it runs. -/
def xiJumps (I : ExecutionEnv .EVM) : Array UInt256 := D_J I.code ⟨0⟩

/-- Mirror of how `Ξ` reports the result of `X`: exceptions propagate, a success
is narrowed to the parts of the machine state a caller can observe, and a revert
keeps the gas `X` reported. -/
def xiResult (r : Except EVM.ExecutionException (ExecutionResult State)) :
    Except EVM.ExecutionException
      (ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)) :=
  match r with
  | .error e => .error e
  | .ok (.success s o) =>
      .ok (.success (s.createdAccounts, s.accountMap, s.gasAvailable, s.substate) o)
  | .ok (.revert g' o) => .ok (.revert g' o)

section Xi

variable {createdAccounts : Std.TreeSet AccountAddress compare} {genesisBlockHeader : BlockHeader}
  {blocks : ProcessedBlocks} {σ σ₀ : AccountMap .EVM} {g : UInt256} {A : Substate}
  {I : ExecutionEnv .EVM}

@[simp] theorem Ξ_zero (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    Ξ 0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfFuel := rfl

/-- **`Ξ` is `X` on a fresh state.**  This is the whole content of the
transaction-level interpreter, and every `X`-level theorem transports across
it. -/
theorem Ξ_succ_eq (fuel : ℕ) (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = xiResult (X fuel (xiJumps I)
          (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)) := by
  show (do
      let result ← X fuel (xiJumps I)
        (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
        | .success evmState' o =>
            .ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap, evmState'.gasAvailable,
                evmState'.substate) o)
        | .revert g' o => .ok (ExecutionResult.revert g' o)) = _
  cases X fuel (xiJumps I) (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) with
  | error e => rfl
  | ok result => cases result <;> rfl

theorem Ξ_succ_of_X_error {fuel : ℕ} {e : EVM.ExecutionException}
    (hX : X fuel (xiJumps I) (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      = .error e) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e := by
  rw [Ξ_succ_eq, hX]; rfl

theorem Ξ_succ_of_X_success {fuel : ℕ} {s : State} {o : ByteArray}
    (hX : X fuel (xiJumps I) (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      = .ok (.success s o)) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = .ok (.success (s.createdAccounts, s.accountMap, s.gasAvailable, s.substate) o) := by
  rw [Ξ_succ_eq, hX]; rfl

theorem Ξ_succ_of_X_revert {fuel : ℕ} {g' : UInt256} {o : ByteArray}
    (hX : X fuel (xiJumps I) (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      = .ok (.revert g' o)) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) := by
  rw [Ξ_succ_eq, hX]; rfl

/-! ### `Ξ` under fuel exhaustion, halting and exceptions

Each theorem below is the `Ξ`-level reading of a run of `X`: the run establishes
how the machine got to its last instruction, and that instruction decides what
the transaction reports. -/

/-- A run that spends all of `Ξ`'s fuel without halting runs out of fuel. -/
theorem Ξ_of_XRuns_outOfFuel {fuel : ℕ} {trace : List Labelled} {post : State}
    (hrun : XRuns (xiJumps I) fuel
      (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace 0 post) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error .OutOfFuel :=
  Ξ_succ_of_X_error hrun.X_outOfFuel

/-- A run ending in a normal halt: `Ξ` reports the observable part of the final
machine state together with the returned data. -/
theorem Ξ_of_XRuns_success {fuel rem : ℕ} {trace : List Labelled}
    {halting mid final : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {gasCost : ℕ} {o : ByteArray}
    (hrun : XRuns (xiJumps I) fuel
      (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z (xiJumps I) w halting = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid final)
    (hH : H final.toMachineState w = some o)
    (hw : w ≠ .REVERT) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = .ok (.success
          (final.createdAccounts, final.accountMap, final.gasAvailable, final.substate) o) :=
  Ξ_succ_of_X_success (hrun.X_success hdec hZ hstep hH hw)

/-- A run ending in a `REVERT`: `Ξ` reports the revert and discards the state. -/
theorem Ξ_of_XRuns_revert {fuel rem : ℕ} {trace : List Labelled}
    {halting mid final : State} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {gasCost : ℕ} {o : ByteArray}
    (hrun : XRuns (xiJumps I) fuel
      (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z (xiJumps I) w halting = .ok (mid, gasCost))
    (hstep : StepOk rem gasCost (w, arg) mid final)
    (hH : H final.toMachineState w = some o)
    (hw : w = .REVERT) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = .ok (.revert final.gasAvailable o) :=
  Ξ_succ_of_X_revert (hrun.X_revert hdec hZ hstep hH hw)

/-- A run reaching an instruction `Z` rejects: `Ξ` raises that exception. -/
theorem Ξ_of_XRuns_exception {fuel rem : ℕ} {trace : List Labelled} {halting : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {e : EVM.ExecutionException}
    (hrun : XRuns (xiJumps I) fuel
      (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z (xiJumps I) w halting = .error e) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  Ξ_succ_of_X_error (hrun.X_exception hdec hZ)

/-- A run reaching an instruction whose execution fails: `Ξ` propagates the
failure. -/
theorem Ξ_of_XRuns_stepError {fuel rem : ℕ} {trace : List Labelled} {halting mid : State}
    {w : Operation .EVM} {arg : Option (UInt256 × Nat)} {gasCost : ℕ}
    {e : EVM.ExecutionException}
    (hrun : XRuns (xiJumps I) fuel
      (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace (rem + 1) halting)
    (hdec : decodeAt halting = (w, arg))
    (hZ : Z (xiJumps I) w halting = .ok (mid, gasCost))
    (hstep : Step rem gasCost (w, arg) mid (.error e)) :
    Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  Ξ_succ_of_X_error (hrun.X_stepError hdec hZ hstep)

/-- **`Ξ` decomposes into a maximal run followed by one terminal event.**  The
run is a real `XRuns` carrying its instructions, its length accounts for exactly
the fuel spent, and the configuration it stops in takes no further iteration —
so by `XStuck.X_terminal` the transaction is out of fuel, raises, or halts. -/
theorem Ξ_decompose (fuel : ℕ) (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    ∃ (trace : List Labelled) (rem : ℕ) (post : State),
      XRuns (xiJumps I) fuel
        (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) trace rem post ∧
      trace.length + rem = fuel ∧
      XStuck (xiJumps I) rem post ∧
      Ξ (fuel + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        = xiResult (X rem (xiJumps I) post) := by
  obtain ⟨trace, rem, post, hrun, heq, hstuck⟩ :=
    X_decompose (xiJumps I) fuel (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
  exact ⟨trace, rem, post, hrun, hrun.length, hstuck, by rw [Ξ_succ_eq, heq]⟩

end Xi

/-! ## Non-vacuity of the `Ξ` layer

The `Ξ_of_XRuns_*` theorems are conditional, so they would hold trivially if no
state could satisfy their hypotheses.  `Ξ_empty_code` discharges them for a real
transaction: a call into an account with no code.  `X` decodes past the end of
the code and gets `STOP` by its own default, which halts successfully, so `Ξ`
returns a success carrying the empty output.

The witness is symbolic in the account map, substate and execution environment —
only the code is fixed — so it does not depend on evaluating a concrete machine
state. -/

theorem C'_STOP (s : State) : C' s .STOP = 0 := by
  simp [C', InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
    InstructionGasGroups.Wzero, GasConstants.Gzero]

/-- `STOP` touches no memory, so it expands none. -/
theorem memoryExpansionCost_STOP (s : State) : memoryExpansionCost s .STOP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

/-- `Z` accepts `STOP` in any state that is not already over the stack limit.
`STOP` is free, so unlike `JUMPDEST` it needs no hypothesis about gas. -/
theorem Z_STOP (validJumps : Array UInt256) (pre : State) (hstack : pre.stack.length ≤ 1024) :
    Z validJumps .STOP pre
      = .ok ({pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0}, 0) := by
  simp only [Z, W, memoryExpansionCost_STOP, C'_STOP]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [δ, α, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [hstack]

/-- The state a `STOP` leaves behind: this instruction's gas paid, and the return
data cleared. -/
def stopPost (gasCost : ℕ) (pre : State) : State :=
  { stepPre gasCost pre with
      toMachineState := (stepPre gasCost pre).toMachineState.setReturnData .empty }

theorem step_STOP (fuel gasCost : ℕ) (pre : State) :
    StepOk (fuel + 1) gasCost (.STOP, none) pre (stopPost gasCost pre) := rfl

@[simp] theorem H_STOP (μ : MachineState) : H μ .STOP = some .empty := rfl

@[simp] theorem xiState_stack (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).stack = [] := rfl

/-- The machine state the immediate `STOP` of an empty-code call halts in. -/
def xiStopped (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) : State :=
  let fresh := xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  stopPost 0 { fresh with gasAvailable := fresh.gasAvailable - UInt256.ofNat 0 }

/-- **`Ξ` really does halt successfully.**  Calling into an account with no code
succeeds with empty output, which instantiates `Ξ_of_XRuns_success` and with it
the whole conditional `Ξ` API. -/
theorem Ξ_empty_code (fuel : ℕ) (createdAccounts : Std.TreeSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) (hcode : I.code = ByteArray.empty) :
    Ξ (fuel + 3) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = xiResult (.ok (.success
          (xiStopped createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ByteArray.empty)) := by
  have hdec : decodeAt (xiState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      = (.STOP, .none) := by
    simp only [decodeAt, xiState, hcode]; rfl
  exact Ξ_of_XRuns_success (rem := fuel + 1) (.refl (fuel + 2) _) hdec
    (Z_STOP _ _ (by simp)) (step_STOP fuel 0 _) (H_STOP _) (by decide)

end EvmYul.EVM.Proof
