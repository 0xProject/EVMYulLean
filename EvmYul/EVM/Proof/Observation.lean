import EvmYul.EVM.Proof.Execution

/-! # Observations and frames

A correspondence proof between two executions never needs the whole post-state:
it needs to know *what an instruction can be observed to change*, and — far more
often — what it cannot. This file supplies both halves for the instructions whose
effects are localized: `SSTORE`, `MSTORE`, `MSTORE8`, `LOG0`–`LOG4`, `RETURN` and
`REVERT`.

The pattern throughout is a pair of theorems per instruction:

* a *step equation*, computing `EvmYul.EVM.step` on a state whose stack is
  explicitly `μ₀ :: μ₁ :: rest`, and
* *frame theorems*, reading each observation off that equation — the one
  component that moves, and the components that do not.

The step equations are stated for a state written `{ pre with stack := … }`
rather than for an arbitrary `pre` constrained by `pre.stack = …`. That is not
cosmetic: with the stack a literal, the `popₙ` in the operation's implementation
reduces, and the whole equation is closed by `rfl`. With the stack behind a
hypothesis it does not reduce, and the proof has to fight `X`'s `CREATE`/`CALL`
branches.
-/

namespace EvmYul

/-! ## Storage is a key-local map -/

namespace Storage

/-- Writing one storage key leaves every other key alone. -/
theorem getD_insert_of_ne (σ : Storage) {k k' v d : UInt256} (h : k ≠ k') :
    (σ.insert k v).getD k' d = σ.getD k' d := by
  rw [Std.TreeMap.getD_insert, ite_eq_right]
  simpa using h

/-- Clearing one storage key leaves every other key alone. -/
theorem getD_erase_of_ne (σ : Storage) {k k' d : UInt256} (h : k ≠ k') :
    (σ.erase k).getD k' d = σ.getD k' d := by
  rw [Std.TreeMap.getD_erase, ite_eq_right]
  simpa using h

theorem getD_insert_self (σ : Storage) {k v d : UInt256} :
    (σ.insert k v).getD k d = v := by
  rw [Std.TreeMap.getD_insert, ite_eq_left]
  simp

theorem getD_erase_self (σ : Storage) {k d : UInt256} :
    (σ.erase k).getD k d = d := by
  rw [Std.TreeMap.getD_erase, ite_eq_left]
  simp

end Storage

/-! ## Account storage is key-local

`Account.updateStorage` is not a plain insert: writing zero *erases* the key, so
that the account's storage stays in the canonical form the state root is computed
from. Both branches are key-local, and both agree with `lookupStorage` at the key
written, which is what makes the distinction invisible to an observer. -/

namespace Account

variable {τ : OperationType}

/-- Reading back the key just written yields the value written — including when
the value is zero and the key was therefore erased rather than inserted. -/
@[simp] theorem lookupStorage_updateStorage_self (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).lookupStorage k = v := by
  unfold updateStorage lookupStorage
  by_cases hv : v = default
  · subst hv
    simp only [beq_self_eq_true, ite_true]
    exact Storage.getD_erase_self _
  · rw [ite_eq_right (by simpa using hv)]
    exact Storage.getD_insert_self _

/-- An `SSTORE` to one key is invisible at every other key of the same account. -/
theorem lookupStorage_updateStorage_of_ne (acc : Account τ) {k k' v : UInt256} (h : k ≠ k') :
    (acc.updateStorage k v).lookupStorage k' = acc.lookupStorage k' := by
  unfold updateStorage lookupStorage
  by_cases hv : v = default
  · rw [ite_eq_left (by simpa using hv)]
    exact Storage.getD_erase_of_ne _ h
  · rw [ite_eq_right (by simpa using hv)]
    exact Storage.getD_insert_of_ne _ h

/-- `updateStorage` touches storage only: nonce, balance, code and transient
storage are untouched. -/
@[simp] theorem updateStorage_nonce (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).nonce = acc.nonce := by
  unfold updateStorage; split <;> rfl

@[simp] theorem updateStorage_balance (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).balance = acc.balance := by
  unfold updateStorage; split <;> rfl

@[simp] theorem updateStorage_code (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).code = acc.code := by
  unfold updateStorage; split <;> rfl

@[simp] theorem updateStorage_tstorage (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).tstorage = acc.tstorage := by
  unfold updateStorage; split <;> rfl

end Account

/-! ## The account map is address-local -/

namespace State

variable {τ : OperationType}

@[simp] theorem lookupAccount_setAccount_self (σ : State τ) (a : AccountAddress) (acc : Account τ) :
    (σ.setAccount a acc).lookupAccount a = some acc := by
  unfold setAccount lookupAccount
  simp

/-- Writing one account leaves every other account alone. This is the frame that
makes "unrelated accounts are untouched" provable. -/
theorem lookupAccount_setAccount_of_ne (σ : State τ) {a b : AccountAddress} (acc : Account τ)
    (h : a ≠ b) : (σ.setAccount a acc).lookupAccount b = σ.lookupAccount b := by
  unfold setAccount lookupAccount
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.get?_eq_getElem?,
    Std.TreeMap.getElem?_insert, ite_eq_right]
  simpa using h

/-- The value an `SLOAD` of `(a, k)` would read: the storage of account `a` at key
`k`, defaulting to zero for an account that does not exist. This is the
observation that a storage-locality statement is about. -/
def storageAt (σ : State τ) (a : AccountAddress) (k : UInt256) : UInt256 :=
  (σ.lookupAccount a).option ⟨0⟩ (Account.lookupStorage (k := k))

theorem storageAt_of_lookup_some {σ : State τ} {a : AccountAddress} {k : UInt256}
    {acc : Account τ} (h : σ.lookupAccount a = some acc) :
    σ.storageAt a k = acc.lookupStorage k := by
  simp only [storageAt, h, Option.option]

/-- An account that does not exist reads as zero at every key, which is what makes
the locality theorems below unconditional. -/
theorem storageAt_of_lookup_none {σ : State τ} {a : AccountAddress} {k : UInt256}
    (h : σ.lookupAccount a = none) : σ.storageAt a k = ⟨0⟩ := by
  simp only [storageAt, h, Option.option]

end State

/-! ## `SSTORE`

`sstore` does three things at once: it writes the key, it warms `(Iₐ, k)`, and it
adjusts the refund counter. Only the first is observable as storage. Every
theorem below is about an *arbitrary* pre-state, so none of them assumes the
account exists — where existence matters it is a hypothesis, and where it does
not (`logSeries`, `executionEnv`) the theorem is unconditional. -/

namespace State

/-- `sstore` is guarded by a lookup of the executing account: with no such
account it is a no-op, so the refund counter and the warm-key set move only on
the branch that actually writes. -/
theorem sstore_of_lookup_none {σ : State .EVM} {k v : UInt256}
    (hacc : σ.lookupAccount σ.executionEnv.codeOwner = none) : σ.sstore k v = σ := by
  simp only [State.sstore, State.lookupAccount] at hacc ⊢
  simp only [hacc, Option.option]

/-- With the executing account present, `sstore` is exactly one account write. -/
theorem sstore_accountMap {σ : State .EVM} {k v : UInt256} {acc : Account .EVM}
    (hacc : σ.lookupAccount σ.executionEnv.codeOwner = some acc) :
    (σ.sstore k v).accountMap
      = σ.accountMap.insert σ.executionEnv.codeOwner (acc.updateStorage k v) := by
  simp only [State.sstore, State.lookupAccount] at hacc ⊢
  simp only [hacc, Option.option]
  rfl

/-- The executing account after an `SSTORE` is the pre-state account with the key
written. -/
theorem lookupAccount_sstore_self {σ : State .EVM} {k v : UInt256} {acc : Account .EVM}
    (hacc : σ.lookupAccount σ.executionEnv.codeOwner = some acc) :
    (σ.sstore k v).lookupAccount σ.executionEnv.codeOwner = some (acc.updateStorage k v) := by
  show (σ.sstore k v).accountMap.get? _ = _
  rw [sstore_accountMap hacc]
  exact lookupAccount_setAccount_self σ _ _

/-- `SSTORE` writes the key it was given. -/
theorem storageAt_sstore_self {σ : State .EVM} {k v : UInt256} {acc : Account .EVM}
    (hacc : σ.lookupAccount σ.executionEnv.codeOwner = some acc) :
    (σ.sstore k v).storageAt σ.executionEnv.codeOwner k = v := by
  rw [storageAt_of_lookup_some (lookupAccount_sstore_self hacc)]
  exact Account.lookupStorage_updateStorage_self acc k v

/-- **Storage key locality.** `SSTORE` is invisible at every other key of the
executing account. -/
theorem storageAt_sstore_of_ne_key {σ : State .EVM} {k k' v : UInt256}
    (h : k ≠ k') :
    (σ.sstore k v).storageAt σ.executionEnv.codeOwner k'
      = σ.storageAt σ.executionEnv.codeOwner k' := by
  cases hacc : σ.lookupAccount σ.executionEnv.codeOwner with
  | none => rw [sstore_of_lookup_none hacc]
  | some acc =>
      rw [storageAt_of_lookup_some (lookupAccount_sstore_self hacc),
        storageAt_of_lookup_some hacc]
      exact Account.lookupStorage_updateStorage_of_ne acc h

/-- **Unrelated accounts.** `SSTORE` writes only the executing account. -/
theorem lookupAccount_sstore_of_ne {σ : State .EVM} {k v : UInt256} {a : AccountAddress}
    (h : a ≠ σ.executionEnv.codeOwner) :
    (σ.sstore k v).lookupAccount a = σ.lookupAccount a := by
  cases hacc : σ.lookupAccount σ.executionEnv.codeOwner with
  | none => rw [sstore_of_lookup_none hacc]
  | some acc =>
      show (σ.sstore k v).accountMap.get? a = _
      rw [sstore_accountMap hacc]
      exact lookupAccount_setAccount_of_ne σ _ (Ne.symm h)

/-- **Unrelated storage.** `SSTORE` is invisible at every key of every other
account: the two locality theorems combined. -/
theorem storageAt_sstore_of_ne_addr {σ : State .EVM} {k k' v : UInt256} {a : AccountAddress}
    (h : a ≠ σ.executionEnv.codeOwner) :
    (σ.sstore k v).storageAt a k' = σ.storageAt a k' := by
  unfold storageAt
  rw [lookupAccount_sstore_of_ne h]

/-- `SSTORE` emits no log. -/
@[simp] theorem sstore_logSeries (σ : State .EVM) (k v : UInt256) :
    (σ.sstore k v).substate.logSeries = σ.substate.logSeries := by
  cases hacc : σ.lookupAccount σ.executionEnv.codeOwner with
  | none => rw [sstore_of_lookup_none hacc]
  | some acc =>
      simp only [State.sstore, State.lookupAccount] at hacc ⊢
      simp only [hacc, Option.option]
      rfl

/-- `SSTORE` does not change who is executing, so iterating the locality
theorems above along a run does not require re-establishing the address. -/
@[simp] theorem sstore_executionEnv (σ : State .EVM) (k v : UInt256) :
    (σ.sstore k v).executionEnv = σ.executionEnv := by
  cases hacc : σ.lookupAccount σ.executionEnv.codeOwner with
  | none => rw [sstore_of_lookup_none hacc]
  | some acc =>
      simp only [State.sstore, State.lookupAccount] at hacc ⊢
      simp only [hacc, Option.option]
      rfl

/-- `SSTORE` does not touch the pre-transaction snapshot the refund is computed
against. -/
@[simp] theorem sstore_σ₀ (σ : State .EVM) (k v : UInt256) : (σ.sstore k v).σ₀ = σ.σ₀ := by
  cases hacc : σ.lookupAccount σ.executionEnv.codeOwner with
  | none => rw [sstore_of_lookup_none hacc]
  | some acc =>
      simp only [State.sstore, State.lookupAccount] at hacc ⊢
      simp only [hacc, Option.option]
      rfl

end State

end EvmYul

namespace EvmYul.EVM.Proof.Observation

open EvmYul EvmYul.EVM EvmYul.EVM.Proof

/-! ## Post-states

`EvmYul.EVM.step` reaches the instructions treated here through three shapes of
combinator: one that rewrites the machine state, one that rewrites the shared
state, and one that appends a log. Naming the three post-states once means each
frame theorem is proved once for a whole family of instructions rather than
once per opcode. -/

/-- The post-state of an instruction that pops two words and rewrites only the
machine state: `MSTORE`, `MSTORE8`, `RETURN`, `REVERT`. -/
def afterMachineOp (gasCost : ℕ) (pre : State)
    (op : MachineState → UInt256 → UInt256 → MachineState) (μ₀ μ₁ : UInt256)
    (rest : Stack UInt256) : State :=
  State.replaceStackAndIncrPC
    { stepPre gasCost pre with
        toMachineState := op (stepPre gasCost pre).toMachineState μ₀ μ₁ } rest

/-- The post-state of an instruction that pops two words and rewrites only the
shared state: `SSTORE`. -/
def afterStateOp (gasCost : ℕ) (pre : State)
    (op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM) (μ₀ μ₁ : UInt256)
    (rest : Stack UInt256) : State :=
  State.replaceStackAndIncrPC
    { stepPre gasCost pre with toState := op (stepPre gasCost pre).toState μ₀ μ₁ } rest

/-- The post-state of `LOGₙ`, which pops the memory range plus `n` topics. -/
def afterLogOp (gasCost : ℕ) (pre : State) (t : Array UInt256) (μ₀ μ₁ : UInt256)
    (rest : Stack UInt256) : State :=
  State.replaceStackAndIncrPC
    { stepPre gasCost pre with
        toSharedState := SharedState.logOp μ₀ μ₁ t (stepPre gasCost pre).toSharedState } rest

/-! ## Step equations

Each of these computes `step` on a state whose stack has the required depth. The
hypothesis form is the one a caller wants, but it is *derived*: the underlying
`rfl` needs the stack as a literal, which `hstack` supplies by rewriting `pre`
into `{ pre with stack := … }` first. -/

theorem step_MSTORE {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.MSTORE, arg)) pre
      = .ok (afterMachineOp gasCost pre MachineState.mstore μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_MSTORE8 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.MSTORE8, arg)) pre
      = .ok (afterMachineOp gasCost pre MachineState.mstore8 μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_RETURN {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.RETURN, arg)) pre
      = .ok (afterMachineOp gasCost pre MachineState.evmReturn μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_REVERT {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.REVERT, arg)) pre
      = .ok (afterMachineOp gasCost pre MachineState.evmRevert μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_SSTORE {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.SSTORE, arg)) pre
      = .ok (afterStateOp gasCost pre EvmYul.State.sstore μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_LOG0 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.LOG0, arg)) pre
      = .ok (afterLogOp gasCost pre #[] μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: rest } by rw [← hstack]]
  rfl

theorem step_LOG1 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ μ₂ : UInt256} {rest : Stack UInt256} (hstack : pre.stack = μ₀ :: μ₁ :: μ₂ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.LOG1, arg)) pre
      = .ok (afterLogOp gasCost pre #[μ₂] μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: μ₂ :: rest } by rw [← hstack]]
  rfl

theorem step_LOG2 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ μ₂ μ₃ : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.LOG2, arg)) pre
      = .ok (afterLogOp gasCost pre #[μ₂, μ₃] μ₀ μ₁ rest) := by
  conv_lhs => rw [show pre = { pre with stack := μ₀ :: μ₁ :: μ₂ :: μ₃ :: rest } by rw [← hstack]]
  rfl

theorem step_LOG3 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ μ₂ μ₃ μ₄ : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.LOG3, arg)) pre
      = .ok (afterLogOp gasCost pre #[μ₂, μ₃, μ₄] μ₀ μ₁ rest) := by
  conv_lhs =>
    rw [show pre = { pre with stack := μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: rest } by rw [← hstack]]
  rfl

theorem step_LOG4 {fuel gasCost : ℕ} {arg : Option (UInt256 × Nat)} {pre : State}
    {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: rest) :
    EvmYul.EVM.step (fuel + 1) gasCost (some (.LOG4, arg)) pre
      = .ok (afterLogOp gasCost pre #[μ₂, μ₃, μ₄, μ₅] μ₀ μ₁ rest) := by
  conv_lhs =>
    rw [show pre = { pre with stack := μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: rest } by rw [← hstack]]
  rfl

/-! ## Frames for machine-state instructions

`MSTORE`, `MSTORE8`, `RETURN` and `REVERT` all leave the world outside the
machine state completely alone, whatever `op` does. These are the theorems that
let a correspondence proof skip such an instruction on the state side. -/

section MachineOpFrame

variable {gasCost : ℕ} {pre : State} {op : MachineState → UInt256 → UInt256 → MachineState}
  {μ₀ μ₁ : UInt256} {rest : Stack UInt256}

/-- **Unrelated accounts.** No machine-state instruction touches any account. -/
@[simp] theorem afterMachineOp_accountMap :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).accountMap = pre.accountMap := rfl

@[simp] theorem afterMachineOp_substate :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).substate = pre.substate := rfl

/-- **Logs.** No machine-state instruction emits a log. -/
@[simp] theorem afterMachineOp_logSeries :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).substate.logSeries = pre.substate.logSeries := rfl

@[simp] theorem afterMachineOp_executionEnv :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).executionEnv = pre.executionEnv := rfl

@[simp] theorem afterMachineOp_stack :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).stack = rest := rfl

@[simp] theorem afterMachineOp_pc :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).pc = pre.pc + UInt256.ofNat 1 := rfl

/-- The machine state is the whole of the effect. -/
@[simp] theorem afterMachineOp_toMachineState :
    (afterMachineOp gasCost pre op μ₀ μ₁ rest).toMachineState
      = op (stepPre gasCost pre).toMachineState μ₀ μ₁ := rfl

end MachineOpFrame

/-! ### `MSTORE` and `MSTORE8`

Memory is the only thing that moves, alongside the active-word count that prices
it. In particular neither writes return data: an `MSTORE` cannot be mistaken for
a halt. -/

section MemoryFrame

variable {gasCost : ℕ} {pre : State} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}

@[simp] theorem afterMachineOp_mstore_memory :
    (afterMachineOp gasCost pre MachineState.mstore μ₀ μ₁ rest).memory
      = (pre.toMachineState.writeWord μ₀ μ₁).memory := rfl

@[simp] theorem afterMachineOp_mstore_activeWords :
    (afterMachineOp gasCost pre MachineState.mstore μ₀ μ₁ rest).activeWords
      = UInt256.ofNat (MachineState.M pre.activeWords.toNat μ₀.toNat 32) := rfl

@[simp] theorem afterMachineOp_mstore_returnData :
    (afterMachineOp gasCost pre MachineState.mstore μ₀ μ₁ rest).returnData = pre.returnData := rfl

@[simp] theorem afterMachineOp_mstore_H_return :
    (afterMachineOp gasCost pre MachineState.mstore μ₀ μ₁ rest).H_return = pre.H_return := rfl

@[simp] theorem afterMachineOp_mstore8_activeWords :
    (afterMachineOp gasCost pre MachineState.mstore8 μ₀ μ₁ rest).activeWords
      = UInt256.ofNat (MachineState.M pre.activeWords.toNat μ₀.toNat 1) := rfl

@[simp] theorem afterMachineOp_mstore8_returnData :
    (afterMachineOp gasCost pre MachineState.mstore8 μ₀ μ₁ rest).returnData = pre.returnData := rfl

@[simp] theorem afterMachineOp_mstore8_H_return :
    (afterMachineOp gasCost pre MachineState.mstore8 μ₀ μ₁ rest).H_return = pre.H_return := rfl

end MemoryFrame

/-! ### `RETURN` and `REVERT`

Both publish a slice of memory as `H_return` and leave memory itself untouched.
They differ only in how `X` reads that slice back out, which is the next section. -/

section ReturnFrame

variable {gasCost : ℕ} {pre : State} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}

/-- `RETURN` publishes exactly the requested memory slice. -/
@[simp] theorem afterMachineOp_evmReturn_H_return :
    (afterMachineOp gasCost pre MachineState.evmReturn μ₀ μ₁ rest).H_return
      = pre.memory.readWithPadding μ₀.toNat μ₁.toNat := rfl

@[simp] theorem afterMachineOp_evmReturn_memory :
    (afterMachineOp gasCost pre MachineState.evmReturn μ₀ μ₁ rest).memory = pre.memory := rfl

/-- `REVERT` publishes the same slice as `RETURN`. -/
@[simp] theorem afterMachineOp_evmRevert_H_return :
    (afterMachineOp gasCost pre MachineState.evmRevert μ₀ μ₁ rest).H_return
      = pre.memory.readWithPadding μ₀.toNat μ₁.toNat := rfl

@[simp] theorem afterMachineOp_evmRevert_memory :
    (afterMachineOp gasCost pre MachineState.evmRevert μ₀ μ₁ rest).memory = pre.memory := rfl

/-- Neither halt refunds gas beyond the cost already charged, so the gas `X`
reports on a `REVERT` is the pre-state gas less this instruction's cost. -/
@[simp] theorem afterMachineOp_evmRevert_gasAvailable :
    (afterMachineOp gasCost pre MachineState.evmRevert μ₀ μ₁ rest).gasAvailable
      = pre.gasAvailable - UInt256.ofNat gasCost := rfl

end ReturnFrame

/-! ## Frames for `SSTORE`

`SSTORE` moves the shared state and nothing else: memory, return data and the
published halting data are all untouched. -/

section StateOpFrame

variable {gasCost : ℕ} {pre : State}
  {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM}
  {μ₀ μ₁ : UInt256} {rest : Stack UInt256}

@[simp] theorem afterStateOp_toState :
    (afterStateOp gasCost pre op μ₀ μ₁ rest).toState = op pre.toState μ₀ μ₁ := rfl

@[simp] theorem afterStateOp_memory :
    (afterStateOp gasCost pre op μ₀ μ₁ rest).memory = pre.memory := rfl

@[simp] theorem afterStateOp_returnData :
    (afterStateOp gasCost pre op μ₀ μ₁ rest).returnData = pre.returnData := rfl

@[simp] theorem afterStateOp_H_return :
    (afterStateOp gasCost pre op μ₀ μ₁ rest).H_return = pre.H_return := rfl

@[simp] theorem afterStateOp_stack :
    (afterStateOp gasCost pre op μ₀ μ₁ rest).stack = rest := rfl

/-- **Storage key locality, at the level of a step.** An `SSTORE` step is
invisible at every other key of the executing account. -/
theorem storageAt_afterStateOp_sstore_of_ne_key {k : UInt256} (h : μ₀ ≠ k) :
    (afterStateOp gasCost pre EvmYul.State.sstore μ₀ μ₁ rest).toState.storageAt
        pre.executionEnv.codeOwner k
      = pre.toState.storageAt pre.executionEnv.codeOwner k := by
  rw [afterStateOp_toState]
  exact EvmYul.State.storageAt_sstore_of_ne_key h

/-- **Unrelated accounts, at the level of a step.** An `SSTORE` step writes only
the executing account. -/
theorem lookupAccount_afterStateOp_sstore_of_ne {a : AccountAddress}
    (h : a ≠ pre.executionEnv.codeOwner) :
    (afterStateOp gasCost pre EvmYul.State.sstore μ₀ μ₁ rest).toState.lookupAccount a
      = pre.toState.lookupAccount a := by
  rw [afterStateOp_toState]
  exact EvmYul.State.lookupAccount_sstore_of_ne h

/-- An `SSTORE` step writes the key it was given. -/
theorem storageAt_afterStateOp_sstore_self {acc : Account .EVM}
    (hacc : pre.toState.lookupAccount pre.executionEnv.codeOwner = some acc) :
    (afterStateOp gasCost pre EvmYul.State.sstore μ₀ μ₁ rest).toState.storageAt
        pre.executionEnv.codeOwner μ₀
      = μ₁ := by
  rw [afterStateOp_toState]
  exact EvmYul.State.storageAt_sstore_self hacc

/-- **Logs.** `SSTORE` emits no log. -/
@[simp] theorem afterStateOp_sstore_logSeries :
    (afterStateOp gasCost pre EvmYul.State.sstore μ₀ μ₁ rest).substate.logSeries
      = pre.substate.logSeries := by
  show (EvmYul.State.sstore pre.toState μ₀ μ₁).substate.logSeries = _
  exact EvmYul.State.sstore_logSeries ..

end StateOpFrame

/-! ## Frames for `LOGₙ`

A log is *appended*: the entry carries the executing account, the topics popped
from the stack, and the memory slice. Nothing else in the substate moves, and no
account does. -/

section LogFrame

variable {gasCost : ℕ} {pre : State} {t : Array UInt256} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}

/-- **Logs.** `LOGₙ` appends exactly one entry, and it is this one. -/
@[simp] theorem afterLogOp_logSeries :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).substate.logSeries
      = pre.substate.logSeries.push
          ⟨pre.executionEnv.codeOwner, t, pre.memory.readWithPadding μ₀.toNat μ₁.toNat⟩ := rfl

/-- **Unrelated accounts.** `LOGₙ` touches no account. -/
@[simp] theorem afterLogOp_accountMap :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).accountMap = pre.accountMap := rfl

@[simp] theorem afterLogOp_memory :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).memory = pre.memory := rfl

@[simp] theorem afterLogOp_returnData :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).returnData = pre.returnData := rfl

@[simp] theorem afterLogOp_H_return :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).H_return = pre.H_return := rfl

@[simp] theorem afterLogOp_executionEnv :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).executionEnv = pre.executionEnv := rfl

@[simp] theorem afterLogOp_refundBalance :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).substate.refundBalance
      = pre.substate.refundBalance := rfl

@[simp] theorem afterLogOp_accessedAccounts :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).substate.accessedAccounts
      = pre.substate.accessedAccounts := rfl

@[simp] theorem afterLogOp_selfDestructSet :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).substate.selfDestructSet
      = pre.substate.selfDestructSet := rfl

@[simp] theorem afterLogOp_stack :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).stack = rest := rfl

/-- The log series only ever grows. -/
theorem afterLogOp_logSeries_size :
    (afterLogOp gasCost pre t μ₀ μ₁ rest).substate.logSeries.size
      = pre.substate.logSeries.size + 1 := by
  rw [afterLogOp_logSeries]; exact Array.size_push ..

end LogFrame

/-! ## Halting classification

`H` — mirrored from `X` in `EvmYul.EVM.Proof.Execution` — decides whether `X`
stops after an instruction. Storing to memory or storage and emitting a log all
continue; `RETURN` and `REVERT` halt, publishing `H_return`. -/

@[simp] theorem H_RETURN (μ : MachineState) : H μ .RETURN = some μ.H_return := rfl
@[simp] theorem H_REVERT (μ : MachineState) : H μ .REVERT = some μ.H_return := rfl
@[simp] theorem H_MSTORE (μ : MachineState) : H μ .MSTORE = none := rfl
@[simp] theorem H_MSTORE8 (μ : MachineState) : H μ .MSTORE8 = none := rfl
@[simp] theorem H_SSTORE (μ : MachineState) : H μ .SSTORE = none := rfl
@[simp] theorem H_LOG0 (μ : MachineState) : H μ .LOG0 = none := rfl
@[simp] theorem H_LOG1 (μ : MachineState) : H μ .LOG1 = none := rfl
@[simp] theorem H_LOG2 (μ : MachineState) : H μ .LOG2 = none := rfl
@[simp] theorem H_LOG3 (μ : MachineState) : H μ .LOG3 = none := rfl
@[simp] theorem H_LOG4 (μ : MachineState) : H μ .LOG4 = none := rfl

/-! ## `X`-level consequences

The step equations and `H` above compose with the decomposition theorems of
`EvmYul.EVM.Proof.Execution` to fix `X`'s result outright. These are the shapes a
`Ξ` correspondence proof consumes: the returned bytes are a named slice of the
pre-state's memory rather than an existential. -/

/-- A `RETURN` that `Z` accepts ends `X` with the memory slice it names. -/
theorem X_RETURN {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.RETURN, arg))
    (hZ : Z validJumps .RETURN pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    X (fuel + 2) validJumps pre
      = .ok (.success (afterMachineOp gasCost mid MachineState.evmReturn μ₀ μ₁ rest)
              (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)) :=
  X_succ_of_halt hdec hZ (step_RETURN hstack) rfl (by simp)

/-- A `REVERT` that `Z` accepts ends `X` with the same slice, reported as a
revert carrying the gas left after the instruction was paid for. -/
theorem X_REVERT {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.REVERT, arg))
    (hZ : Z validJumps .REVERT pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    X (fuel + 2) validJumps pre
      = .ok (.revert (mid.gasAvailable - UInt256.ofNat gasCost)
              (mid.memory.readWithPadding μ₀.toNat μ₁.toNat)) :=
  X_succ_of_revert (fuel := fuel + 1) hdec hZ (step_REVERT hstack)
    (o := mid.memory.readWithPadding μ₀.toNat μ₁.toNat) rfl rfl

/-- `SSTORE`, `MSTORE`, `MSTORE8` and `LOGₙ` do not halt, so each is one
non-halting iteration of `X` and the run continues at one less fuel. -/
theorem xStepAt_SSTORE {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.SSTORE, arg))
    (hZ : Z validJumps .SSTORE pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre
      (afterStateOp gasCost mid EvmYul.State.sstore μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_SSTORE hstack
  · rw [hdec]; simp

theorem xStepAt_MSTORE {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.MSTORE, arg))
    (hZ : Z validJumps .MSTORE pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre
      (afterMachineOp gasCost mid MachineState.mstore μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_MSTORE hstack
  · rw [hdec]; simp

theorem xStepAt_LOG0 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.LOG0, arg))
    (hZ : Z validJumps .LOG0 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre (afterLogOp gasCost mid #[] μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_LOG0 hstack
  · rw [hdec]; simp

theorem xStepAt_MSTORE8 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.MSTORE8, arg))
    (hZ : Z validJumps .MSTORE8 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre
      (afterMachineOp gasCost mid MachineState.mstore8 μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_MSTORE8 hstack
  · rw [hdec]; simp

theorem xStepAt_LOG1 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ μ₂ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.LOG1, arg))
    (hZ : Z validJumps .LOG1 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: μ₂ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre (afterLogOp gasCost mid #[μ₂] μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_LOG1 hstack
  · rw [hdec]; simp

theorem xStepAt_LOG2 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ μ₂ μ₃ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.LOG2, arg))
    (hZ : Z validJumps .LOG2 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre (afterLogOp gasCost mid #[μ₂, μ₃] μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_LOG2 hstack
  · rw [hdec]; simp

theorem xStepAt_LOG3 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ μ₂ μ₃ μ₄ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.LOG3, arg))
    (hZ : Z validJumps .LOG3 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre
      (afterLogOp gasCost mid #[μ₂, μ₃, μ₄] μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_LOG3 hstack
  · rw [hdec]; simp

theorem xStepAt_LOG4 {fuel gasCost : ℕ} {validJumps : Array UInt256} {pre mid : State}
    {arg : Option (UInt256 × Nat)} {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ : UInt256} {rest : Stack UInt256}
    (hdec : decodeAt pre = (.LOG4, arg))
    (hZ : Z validJumps .LOG4 pre = .ok (mid, gasCost))
    (hstack : mid.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: rest) :
    XStepAt validJumps (fuel + 1) gasCost pre
      (afterLogOp gasCost mid #[μ₂, μ₃, μ₄, μ₅] μ₀ μ₁ rest) := by
  refine ⟨mid, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]; exact step_LOG4 hstack
  · rw [hdec]; simp

end EvmYul.EVM.Proof.Observation
