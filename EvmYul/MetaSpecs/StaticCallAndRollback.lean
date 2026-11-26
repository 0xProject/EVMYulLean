import EvmYul.Yul.MessageCallCombinator
import EvmYul.SharedStateOps
import EvmYul.EVM.Exception

namespace EvmYul

namespace MetaSpec

open EvmYul.Yul
open EvmYul.EVM

/-!
# Meta-Specifications: StaticCall Immutability & Transactional Rollback

Formalizes `MetaSpec.StaticCallImmutability` and `MetaSpec.TransactionalRollback`
for `EVMYulLean 2.0`:
1. **`StaticCallImmutability`**: When `perm = false`, any guarded state transition or
   child call environment preserves `perm = false` and leaves world state `accountMap`,
   transient storage `tstorage`, `createdAccounts`, and `substate.logSeries` (`logs`) invariant.
2. **`TransactionalRollback`**: Exact checkpoint restoration
   `(σ_checkpoint, tstorage_checkpoint, logs_checkpoint)` on `REVERT` vs exceptional halt,
   where `REVERT` preserves remaining gas `avail - memCost` while exceptional halt burns
   all frame gas to `0`.
-/

/-- Extract the transient storage (`tstorage`) for a given account address `addr` from `State τ`. -/
def accountTStorage {τ : OperationType} (s : EvmYul.State τ) (addr : AccountAddress) : Storage :=
  match s.accountMap.get? addr with
  | none => default
  | some acc => acc.tstorage

/-- Extract the accrued log series (`substate.logSeries`) from `State τ`. -/
def stateLogs {τ : OperationType} (s : EvmYul.State τ) : LogSeries :=
  s.substate.logSeries

/-- Predicate classifying state-mutating operations prohibited when `perm = false`
    (Yellow Paper Eq. 159 / EIP-214 `STATICCALL` write guard). -/
def isStateMutatingOp {τ : OperationType} (op : Operation τ) (callVal : UInt256) : Bool :=
  match op with
  | .CREATE | .CREATE2 | .SSTORE | .SELFDESTRUCT
  | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 | .TSTORE => true
  | .CALL => callVal != ⟨0⟩
  | _ => false

/-- Static-mode guard check: throws `.StaticModeViolation` precisely when `perm = false`
    and the operation is state-mutating. -/
def checkStaticPerm {τ : OperationType} (perm : Bool) (op : Operation τ) (callVal : UInt256) :
    Except ExecutionException Unit :=
  if !perm && isStateMutatingOp op callVal then
    .error .StaticModeViolation
  else
    .ok ()

/-- A guarded state transition wraps a raw transition `stepFn`, rejecting state-mutating
    operations with `.StaticModeViolation` when `s.executionEnv.perm = false`. -/
def guardedTransition {τ : OperationType}
    (op : Operation τ) (callVal : UInt256)
    (stepFn : SharedState τ → SharedState τ)
    (s : SharedState τ) : Except ExecutionException (SharedState τ) := do
  checkStaticPerm s.executionEnv.perm op callVal
  return stepFn s

/-- Proposition characterizing when a transition function `stepFn` respects read-only world-state
    invariance whenever `isStateMutatingOp op callVal = false`. -/
def RespectsStaticInvariance {τ : OperationType}
    (op : Operation τ) (callVal : UInt256) (stepFn : SharedState τ → SharedState τ) : Prop :=
  isStateMutatingOp op callVal = false →
    ∀ s : SharedState τ,
      (stepFn s).executionEnv.perm = s.executionEnv.perm ∧
      (stepFn s).accountMap = s.accountMap ∧
      (∀ addr, accountTStorage (stepFn s).toState addr = accountTStorage s.toState addr) ∧
      (stepFn s).createdAccounts = s.createdAccounts ∧
      stateLogs (stepFn s).toState = stateLogs s.toState

/-- `MetaSpec.StaticCallImmutability`:
    When `s.executionEnv.perm = false`, any guarded state transition and any child call
    environment constructed via `prepareChildCallEnv` preserves `perm = false` and leaves
    `accountMap`, `tstorage`, `createdAccounts`, and `substate.logSeries` (`logs`) invariant. -/
structure StaticCallImmutability {τ : OperationType}
    (s s' : SharedState τ) : Prop where
  perm_false_preserved : s.executionEnv.perm = false → s'.executionEnv.perm = false
  accountMap_invariant : s.executionEnv.perm = false → s'.accountMap = s.accountMap
  tstorage_invariant   : s.executionEnv.perm = false →
    ∀ addr : AccountAddress, accountTStorage s'.toState addr = accountTStorage s.toState addr
  created_invariant    : s.executionEnv.perm = false → s'.createdAccounts = s.createdAccounts
  logs_invariant       : s.executionEnv.perm = false → stateLogs s'.toState = stateLogs s.toState

/-- Snapshot checkpoint of world state, transient storage map projection, created accounts, and logs
    taken before entering a message-call or creation frame. -/
structure CallFrameCheckpoint (τ : OperationType) where
  σ_checkpoint        : AccountMap τ
  tstorage_checkpoint : AccountAddress → Storage
  created_checkpoint  : Std.TreeSet AccountAddress compare
  logs_checkpoint     : LogSeries

/-- Capture the checkpoint `(σ_checkpoint, tstorage_checkpoint, created_checkpoint, logs_checkpoint)`
    from a pre-call `State τ`. -/
def takeCheckpoint {τ : OperationType} (s : EvmYul.State τ) : CallFrameCheckpoint τ where
  σ_checkpoint        := s.accountMap
  tstorage_checkpoint := accountTStorage s
  created_checkpoint  := s.createdAccounts
  logs_checkpoint     := stateLogs s

/-- Outcome of a message call or contract creation frame prior to checkpoint reconciliation. -/
inductive FrameTermination where
  | Return (avail memCost : ℕ) (retData : ByteArray)
  | Revert (avail memCost : ℕ) (retData : ByteArray)
  | ExceptionalHalt (err : ExecutionException)
  deriving Repr

/-- Post-frame state and remaining gas after reconciling a `FrameTermination` against `ckpt`:
    - `Return`: commits post-frame state `postState` and returns `avail - memCost` gas.
    - `Revert`: rolls back `accountMap`, `createdAccounts`, and `substate.logSeries` to `ckpt`,
      and refunds remaining gas `avail - memCost`.
    - `ExceptionalHalt`: rolls back `accountMap`, `createdAccounts`, and `substate.logSeries`
      to `ckpt`, burns all frame gas to `0`, and clears return data. -/
def resolveFrameTermination {τ : OperationType}
    (ckpt : CallFrameCheckpoint τ)
    (postState : EvmYul.State τ)
    (term : FrameTermination) : EvmYul.State τ × ℕ × Bool × ByteArray :=
  match term with
  | .Return avail memCost retData =>
    (postState, avail - memCost, true, retData)
  | .Revert avail memCost retData =>
    let rolledBack : EvmYul.State τ :=
      { postState with
        accountMap := ckpt.σ_checkpoint
        createdAccounts := ckpt.created_checkpoint
        substate := { postState.substate with logSeries := ckpt.logs_checkpoint } }
    (rolledBack, avail - memCost, false, retData)
  | .ExceptionalHalt _ =>
    let rolledBack : EvmYul.State τ :=
      { postState with
        accountMap := ckpt.σ_checkpoint
        createdAccounts := ckpt.created_checkpoint
        substate := { postState.substate with logSeries := ckpt.logs_checkpoint } }
    (rolledBack, 0, false, ByteArray.empty)

/-- `MetaSpec.TransactionalRollback`:
    Relates pre-frame state `preState`, mutated mid-frame state `postState`, and termination `term`:
    both `REVERT` and `ExceptionalHalt` restore `(σ_checkpoint, tstorage_checkpoint, logs_checkpoint)`
    from `takeCheckpoint preState`, while `REVERT` preserves remaining gas `avail - memCost` and
    `ExceptionalHalt` burns all frame gas to `0`. -/
def TransactionalRollback {τ : OperationType}
    (preState postState : EvmYul.State τ)
    (avail memCost : ℕ) (retData : ByteArray) (err : ExecutionException) : Prop :=
  let ckpt := takeCheckpoint preState
  let (revState, revGas, revSuccess, revOut) :=
    resolveFrameTermination ckpt postState (.Revert avail memCost retData)
  let (haltState, haltGas, haltSuccess, haltOut) :=
    resolveFrameTermination ckpt postState (.ExceptionalHalt err)
  revState.accountMap = ckpt.σ_checkpoint ∧
  (∀ addr, accountTStorage revState addr = ckpt.tstorage_checkpoint addr) ∧
  stateLogs revState = ckpt.logs_checkpoint ∧
  revGas = avail - memCost ∧
  revSuccess = false ∧
  revOut = retData ∧
  haltState.accountMap = ckpt.σ_checkpoint ∧
  (∀ addr, accountTStorage haltState addr = ckpt.tstorage_checkpoint addr) ∧
  stateLogs haltState = ckpt.logs_checkpoint ∧
  haltGas = 0 ∧
  haltSuccess = false ∧
  haltOut = ByteArray.empty

-- ============================================================================
-- Theorems for StaticCallImmutability & TransactionalRollback
-- ============================================================================

/-- Theorem 1: Child call environment permission monotonicity & `STATICCALL` enforcement.
    Whenever parent `perm = false` or the call mode is `.StaticCall`, `prepareChildCallEnv`
    produces a child environment with `perm = false`. -/
theorem prepareChildCallEnv_perm_false
    (mode : YulCallMode) (parentEnv : ExecutionEnv .Yul)
    (params : YulCallParams) (cd : ByteArray)
    (h : parentEnv.perm = false ∨ mode = .StaticCall) :
    (prepareChildCallEnv mode parentEnv params cd).perm = false := by
  unfold prepareChildCallEnv
  dsimp
  rcases h with hperm | rfl
  · rw [hperm]
    exact effectivePerm_preserves_false mode
  · exact effectivePerm_staticCall parentEnv.perm

/-- Theorem 2: In static mode (`perm = false`), every state-mutating operation (`SSTORE`, `TSTORE`,
    `LOG0`..`LOG4`, `CREATE`, `CREATE2`, `SELFDESTRUCT`, value-bearing `CALL`) is rejected by
    `guardedTransition` with `.error .StaticModeViolation`. -/
theorem guardedTransition_rejects_mutating_when_static {τ : OperationType}
    (op : Operation τ) (callVal : UInt256)
    (stepFn : SharedState τ → SharedState τ)
    (s : SharedState τ)
    (hPerm : s.executionEnv.perm = false)
    (hMut : isStateMutatingOp op callVal = true) :
    guardedTransition op callVal stepFn s = .error .StaticModeViolation := by
  unfold guardedTransition checkStaticPerm
  rw [hPerm, hMut]
  rfl

/-- Theorem 3: Any guarded transition that succeeds (`guardedTransition ... = .ok s'`) from a
    static state (`s.executionEnv.perm = false`) under a transition respecting static invariance
    satisfies `StaticCallImmutability s s'`. -/
theorem guardedTransition_staticCallImmutability {τ : OperationType}
    (op : Operation τ) (callVal : UInt256)
    (stepFn : SharedState τ → SharedState τ)
    (s s' : SharedState τ)
    (hResp : RespectsStaticInvariance op callVal stepFn)
    (hStep : guardedTransition op callVal stepFn s = .ok s') :
    StaticCallImmutability s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro hPerm
  all_goals
    unfold guardedTransition checkStaticPerm at hStep
    rw [hPerm] at hStep
    cases hMut : isStateMutatingOp op callVal
    · rw [hMut] at hStep
      dsimp at hStep
      injection hStep with hEq
      subst hEq
      have ⟨h1, h2, h3, h4, h5⟩ := hResp hMut s
      first
      | exact h1.trans hPerm
      | exact h2
      | exact h3
      | exact h4
      | exact h5
    · rw [hMut] at hStep
      contradiction

/-- Theorem 4: SharedState memory operations (`writeWord`, `calldatacopy`, `codeCopy`) satisfy
    `StaticCallImmutability` unconditionally (they never mutate `accountMap`, `tstorage`,
    `createdAccounts`, `substate.logSeries`, or `executionEnv.perm`). -/
theorem sharedState_memoryOps_staticCallImmutability
    (s : SharedState .EVM) (addr val mstart dstart size : UInt256) :
    StaticCallImmutability s (s.writeWord addr val) ∧
    StaticCallImmutability s (s.calldatacopy mstart dstart size) ∧
    StaticCallImmutability s (s.codeCopy mstart dstart size) := by
  refine ⟨⟨fun h => h, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩,
          ⟨fun h => h, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩,
          ⟨fun h => h, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩

/-- Theorem 5: Read-only world-state queries (`sload`, `tload`, `balance`, `extCodeSize`)
    warm accessed sets in `substate` without modifying `accountMap`, `tstorage`,
    `createdAccounts`, `substate.logSeries`, or `executionEnv.perm`. -/
theorem state_readOps_preserve_world_and_logs {τ : OperationType}
    (s : EvmYul.State τ) (k : UInt256) :
    let s_sload := (s.sload k).1
    let s_tload := (s.tload k).1
    let s_bal   := (s.balance k).1
    s_sload.accountMap = s.accountMap ∧
    (∀ addr, accountTStorage s_sload addr = accountTStorage s addr) ∧
    stateLogs s_sload = stateLogs s ∧
    s_tload.accountMap = s.accountMap ∧
    (∀ addr, accountTStorage s_tload addr = accountTStorage s addr) ∧
    stateLogs s_tload = stateLogs s ∧
    s_bal.accountMap = s.accountMap ∧
    (∀ addr, accountTStorage s_bal addr = accountTStorage s addr) ∧
    stateLogs s_bal = stateLogs s := by
  refine ⟨rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, rfl⟩

/-- Theorem 6: `MetaSpec.TransactionalRollback` holds universally for any pre-frame state
    `preState`, arbitrary mid-frame dirty state `postState` (even after `sstore`, `tstore`,
    `logOp`), gas parameters `(avail, memCost)`, return buffer `retData`, and exception `err`. -/
theorem transactionalRollback_universal {τ : OperationType}
    (preState postState : EvmYul.State τ)
    (avail memCost : ℕ) (retData : ByteArray) (err : ExecutionException) :
    TransactionalRollback preState postState avail memCost retData err := by
  unfold TransactionalRollback resolveFrameTermination takeCheckpoint accountTStorage stateLogs
  exact ⟨rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 7: Tight gas accounting distinction between `REVERT` and `ExceptionalHalt`:
    when `memCost < avail`, `REVERT` refunds strictly positive gas (`0 < revGas`) equal to
    `avail - memCost`, whereas `ExceptionalHalt` burns all frame gas (`haltGas = 0`), so
    `haltGas < revGas`. -/
theorem revert_vs_exceptionalHalt_gas_strict {τ : OperationType}
    (ckpt : CallFrameCheckpoint τ) (postState : EvmYul.State τ)
    (avail memCost : ℕ) (retData : ByteArray) (err : ExecutionException)
    (hLt : memCost < avail) :
    let (_, revGas, _, _) := resolveFrameTermination ckpt postState (.Revert avail memCost retData)
    let (_, haltGas, _, _) := resolveFrameTermination ckpt postState (.ExceptionalHalt err)
    revGas = avail - memCost ∧ haltGas = 0 ∧ haltGas < revGas := by
  dsimp [resolveFrameTermination]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- Theorem 8: End-to-end rollback after dirtying persistent storage (`sstore`), transient
    storage (`tstore`), and logs (`logOp`): resolving with `.Revert` or `.ExceptionalHalt`
    against `takeCheckpoint s.toState` completely erases all three mutations and restores
    `(s.accountMap, accountTStorage s.toState, stateLogs s.toState)`. -/
theorem rollback_erases_sstore_tstore_and_logs {τ : OperationType}
    (s : SharedState τ) (k v μ₀ μ₁ : UInt256) (topics : Array UInt256)
    (avail memCost : ℕ) (retData : ByteArray) :
    let dirtyState : SharedState τ :=
      SharedState.logOp μ₀ μ₁ topics
        { s with toState := (s.toState.sstore k v).tstore k v }
    let ckpt := takeCheckpoint s.toState
    let (revState, revGas, _, _) :=
      resolveFrameTermination ckpt dirtyState.toState (.Revert avail memCost retData)
    revState.accountMap = s.accountMap ∧
    (∀ addr, accountTStorage revState addr = accountTStorage s.toState addr) ∧
    revState.createdAccounts = s.createdAccounts ∧
    stateLogs revState = stateLogs s.toState ∧
    revGas = avail - memCost := by
  dsimp [resolveFrameTermination, takeCheckpoint, accountTStorage, stateLogs]
  exact ⟨rfl, fun _ => rfl, rfl, rfl, rfl⟩

end MetaSpec

end EvmYul
