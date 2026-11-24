import EvmYul.Semantics
import EvmYul.Yul.GasInterpreter
import EvmYul.EVM.Gas

/-!
Dialect-independent effects of shared instructions, with bridges to the actual
`step` functions. Stack/PC and Yul variable stores are administrative state.
Code is deliberately not equated: bytecode and Yul ASTs have different types.
Halting conventions are stated explicitly below; in particular Yul REVERT
forgets its state, and STOP clears EVM returnData only.
-/
namespace EvmYul.MetaSpec.DialectCommutation

open EvmYul EVM GasConstants

/-- Storage observations include the missing-account/default-zero behavior. -/
def storageAt {τ} (s : SharedState τ) (k : UInt256) : UInt256 :=
  s.toState.lookupAccount s.executionEnv.codeOwner |>.option ⟨0⟩
    (Account.lookupStorage (k := k))

def transientAt {τ} (s : SharedState τ) (k : UInt256) : UInt256 :=
  s.toState.lookupAccount s.executionEnv.codeOwner |>.option ⟨0⟩
    (Account.lookupTransientStorage (k := k))

/-- All state observations used by the shared instructions, including memory,
    gas, logs, access sets and both storage spaces. No restriction on code. -/
structure Related (y : SharedState .Yul) (e : SharedState .EVM) : Prop where
  machine : y.toMachineState = e.toMachineState
  substate : y.substate = e.substate
  owner : y.executionEnv.codeOwner = e.executionEnv.codeOwner
  calldata : y.executionEnv.calldata = e.executionEnv.calldata
  storage : ∀ k, storageAt y k = storageAt e k
  transient : ∀ k, transientAt y k = transientAt e k

def withMachine {τ} (s : SharedState τ) (m : MachineState) : SharedState τ :=
  { s with toMachineState := m }

/-- Replacing a common machine state preserves every other shared observation. -/
theorem machine_commutes (y : SharedState .Yul) (e : SharedState .EVM)
    (h : Related y e) (m : MachineState) :
    Related (withMachine y m) (withMachine e m) := by
  exact ⟨rfl, h.substate, h.owner, h.calldata, h.storage, h.transient⟩

def load {τ} (s : SharedState τ) (k : UInt256) : SharedState τ × UInt256 :=
  let (s', v) := s.toState.sload k
  ({ s with toState := s' }, v)

def tload {τ} (s : SharedState τ) (k : UInt256) : SharedState τ × UInt256 :=
  let (s', v) := s.toState.tload k
  ({ s with toState := s' }, v)

/-- SLOAD agrees on its value AND warms the same key in the access substate. -/
theorem sload_commutes (y : SharedState .Yul) (e : SharedState .EVM)
    (h : Related y e) (k : UInt256) :
    Related (load y k).1 (load e k).1 ∧ (load y k).2 = (load e k).2 := by
  constructor
  · refine ⟨h.machine, ?_, h.owner, h.calldata, h.storage, h.transient⟩
    change y.substate.addAccessedStorageKey (y.executionEnv.codeOwner, k) =
      e.substate.addAccessedStorageKey (e.executionEnv.codeOwner, k)
    rw [h.substate, h.owner]
  · exact h.storage k

/-- TLOAD agrees without warming a key or modifying the shared state. -/
theorem tload_commutes (y : SharedState .Yul) (e : SharedState .EVM)
    (h : Related y e) (k : UInt256) :
    Related (tload y k).1 (tload e k).1 ∧ (tload y k).2 = (tload e k).2 := by
  exact ⟨h, h.transient k⟩

/-- CALLDATACOPY agrees on memory and active words as well as preserved storage. -/
theorem calldatacopy_commutes (y : SharedState .Yul) (e : SharedState .EVM)
    (h : Related y e) (dst src size : UInt256) :
    Related (y.calldatacopy dst src size) (e.calldatacopy dst src size) := by
  refine ⟨?_, h.substate, h.owner, h.calldata, h.storage, h.transient⟩
  change { y.toMachineState with
    memory := y.executionEnv.calldata.write src.toNat y.memory dst.toNat size.toNat
    activeWords := .ofNat (MachineState.M y.activeWords.toNat dst.toNat size.toNat) } =
    { e.toMachineState with
    memory := e.executionEnv.calldata.write src.toNat e.memory dst.toNat size.toNat
    activeWords := .ofNat (MachineState.M e.activeWords.toNat dst.toNat size.toNat) }
  have hm := h.machine
  have hc := h.calldata
  cases y; cases e
  simp_all

/-- Every LOG topic count uses the same byte slice, owner, topic order and
    memory expansion. This includes LOG0 through LOG4. -/
theorem log_commutes (y : SharedState .Yul) (e : SharedState .EVM)
    (h : Related y e) (offset size : UInt256) (topics : Array UInt256) :
    Related (SharedState.logOp offset size topics y)
      (SharedState.logOp offset size topics e) := by
  refine ⟨?_, ?_, h.owner, h.calldata, h.storage, h.transient⟩
  · change { y.toMachineState with activeWords := UInt256.ofNat (MachineState.M y.activeWords.toNat offset.toNat size.toNat) } =
      { e.toMachineState with activeWords := UInt256.ofNat (MachineState.M e.activeWords.toNat offset.toNat size.toNat) }
    have hm := h.machine
    cases y; cases e
    simp_all
  · change { y.substate with logSeries := y.substate.logSeries.push (
        ⟨y.executionEnv.codeOwner, topics, y.memory.readWithPadding offset.toNat size.toNat⟩) } =
      { e.substate with logSeries := e.substate.logSeries.push (
        ⟨e.executionEnv.codeOwner, topics, e.memory.readWithPadding offset.toNat size.toNat⟩) }
    have hm : y.memory = e.memory := congrArg MachineState.memory h.machine
    rw [h.substate, h.owner, hm]

inductive Binary where
  | add | sub | mul | div | mod | xor | and | or | exp

def Binary.op (τ : OperationType) : Binary → Operation τ
  | .add => .ADD | .sub => .SUB | .mul => .MUL | .div => .DIV
  | .mod => .MOD | .xor => .XOR | .and => .AND | .or => .OR | .exp => .EXP

def Binary.fn : Binary → UInt256 → UInt256 → UInt256
  | .add => UInt256.add | .sub => UInt256.sub | .mul => UInt256.mul
  | .div => UInt256.div | .mod => UInt256.mod | .xor => UInt256.xor
  | .and => UInt256.land | .or => UInt256.lor | .exp => UInt256.exp

/-- Instructions carry exactly their required arguments. -/
inductive Instruction where
  | binary (op : Binary) (a b : UInt256)
  | sload (key : UInt256)
  | tload (key : UInt256)
  | keccak (offset size : UInt256)
  | log0 (offset size : UInt256)
  | log1 (offset size t0 : UInt256)
  | log2 (offset size t0 t1 : UInt256)
  | log3 (offset size t0 t1 t2 : UInt256)
  | log4 (offset size t0 t1 t2 t3 : UInt256)
  | calldatacopy (dst src size : UInt256)
  | mcopy (dst src size : UInt256)
  | stop
  | ret (offset size : UInt256)
  | revert (offset size : UInt256)

def Instruction.op (τ : OperationType) : Instruction → Operation τ
  | .binary b _ _ => b.op τ
  | .sload _ => .SLOAD | .tload _ => .TLOAD | .keccak _ _ => .KECCAK256
  | .log0 .. => .LOG0 | .log1 .. => .LOG1 | .log2 .. => .LOG2
  | .log3 .. => .LOG3 | .log4 .. => .LOG4
  | .calldatacopy .. => .CALLDATACOPY | .mcopy .. => .MCOPY
  | .stop => .STOP | .ret .. => .RETURN | .revert .. => .REVERT

def Instruction.args : Instruction → List UInt256
  | .binary _ a b => [a,b] | .sload k => [k] | .tload k => [k]
  | .keccak a b | .log0 a b | .ret a b | .revert a b => [a,b]
  | .log1 a b c => [a,b,c] | .log2 a b c d => [a,b,c,d]
  | .log3 a b c d e => [a,b,c,d,e] | .log4 a b c d e f => [a,b,c,d,e,f]
  | .calldatacopy a b c | .mcopy a b c => [a,b,c]
  | .stop => []

/-- Shared primitive effects. REVERT's effect is before Yul discards its state;
    STOP here retains state, and the actual EVM bridge requires empty returnData. -/
def effect {τ} (i : Instruction) (s : SharedState τ) : SharedState τ × Option UInt256 :=
  match i with
  | .binary b a c => (s, some (b.fn a c))
  | .sload k => let (s', v) := load s k; (s', some v)
  | .tload k => let (s', v) := tload s k; (s', some v)
  | .keccak a b => let (v, m) := s.toMachineState.keccak256 a b; (withMachine s m, some v)
  | .log0 a b => (SharedState.logOp a b #[] s, none)
  | .log1 a b c => (SharedState.logOp a b #[c] s, none)
  | .log2 a b c d => (SharedState.logOp a b #[c,d] s, none)
  | .log3 a b c d e => (SharedState.logOp a b #[c,d,e] s, none)
  | .log4 a b c d e f => (SharedState.logOp a b #[c,d,e,f] s, none)
  | .calldatacopy a b c => (s.calldatacopy a b c, none)
  | .mcopy a b c => (withMachine s (s.toMachineState.mcopy a b c), none)
  | .stop => (s, none)
  | .ret a b => (withMachine s (s.toMachineState.evmReturn a b), none)
  | .revert a b => (withMachine s (s.toMachineState.evmRevert a b), none)

/-- The full shared effect commutes for every listed instruction: equal result
    values and related resulting SharedStates, including gas and memory. -/
theorem effects_commute (i : Instruction) (y : SharedState .Yul)
    (e : SharedState .EVM) (h : Related y e) :
    Related (effect i y).1 (effect i e).1 ∧ (effect i y).2 = (effect i e).2 := by
  cases i with
  | binary => exact ⟨h, rfl⟩
  | sload k =>
    have hh := sload_commutes y e h k
    exact ⟨hh.1, congrArg some hh.2⟩
  | tload k =>
    have hh := tload_commutes y e h k
    exact ⟨hh.1, congrArg some hh.2⟩
  | keccak a b =>
    change Related (withMachine y (y.toMachineState.keccak256 a b).2)
      (withMachine e (e.toMachineState.keccak256 a b).2) ∧
      some (y.toMachineState.keccak256 a b).1 = some (e.toMachineState.keccak256 a b).1
    rw [h.machine]
    exact ⟨machine_commutes y e h _, rfl⟩
  | log0 a b => exact ⟨log_commutes y e h a b #[], rfl⟩
  | log1 a b c => exact ⟨log_commutes y e h a b #[c], rfl⟩
  | log2 a b c d => exact ⟨log_commutes y e h a b #[c,d], rfl⟩
  | log3 a b c d f => exact ⟨log_commutes y e h a b #[c,d,f], rfl⟩
  | log4 a b c d f g => exact ⟨log_commutes y e h a b #[c,d,f,g], rfl⟩
  | calldatacopy a b c => exact ⟨calldatacopy_commutes y e h a b c, rfl⟩
  | mcopy a b c =>
    change Related (withMachine y _) (withMachine e _) ∧ _
    rw [h.machine]
    exact ⟨machine_commutes y e h _, rfl⟩
  | stop => exact ⟨h, rfl⟩
  | ret a b =>
    change Related (withMachine y _) (withMachine e _) ∧ _
    rw [h.machine]
    exact ⟨machine_commutes y e h _, rfl⟩
  | revert a b =>
    change Related (withMachine y _) (withMachine e _) ∧ _
    rw [h.machine]
    exact ⟨machine_commutes y e h _, rfl⟩

/-- Expected Yul outcome, preserving the implementation's halting convention. -/
def yulOutcome (i : Instruction) (s : SharedState .Yul) (vs : Yul.VarStore) :
    Except Yul.Exception (Yul.State × Option UInt256) :=
  let (s', v) := effect i s
  match i with
  | .stop => .error (.YulHalt (.Ok s' vs) ⟨0⟩)
  | .ret .. => .error (.YulHalt (.Ok s' vs) ⟨1⟩)
  | .revert .. => .error (.Revert s'.H_return)
  | _ => .ok (.Ok s' vs, v)

/-- Every effect above is connected to the real Yul semantics, not a separate
    unverified opcode model. -/
theorem yul_step_effect (i : Instruction) (s : SharedState .Yul) (vs : Yul.VarStore) :
    step (i.op .Yul) none (.Ok s vs) i.args = yulOutcome i s vs := by
  cases i with
  | binary b a c => cases b <;> rfl
  | sload | tload | keccak | log0 | log1 | log2 | log3 | log4
  | calldatacopy | mcopy | stop | ret | revert => rfl

/-- EVM administrative state after an instruction, retaining an arbitrary tail. -/
def evmOutcome (i : Instruction) (s : EVM.State) (tail : List UInt256) : EVM.State :=
  let (s', v) := effect i s.toSharedState
  match i with
  | .stop => s
  | _ =>
    ({ s with toSharedState := s' }).replaceStackAndIncrPC
      (match v with | some v => v :: tail | none => tail)

/-- The EVM uses the identical shared effects. STOP's precise necessary
    precondition is explicit: Yul STOP does not clear a nonempty returnData. -/
theorem evm_step_effect (i : Instruction) (s : EVM.State) (tail : List UInt256)
    (hstop : i = .stop → s.returnData = ByteArray.empty) :
    step (i.op .EVM) none {s with stack := i.args ++ tail} =
      .ok (evmOutcome i {s with stack := i.args ++ tail} tail) := by
  cases i with
  | binary b a c => cases b <;> rfl
  | sload | tload | keccak | log0 | log1 | log2 | log3 | log4
  | calldatacopy | mcopy | ret | revert => rfl
  | stop =>
    have hs := hstop rfl
    change Except.ok { s with stack := tail, returnData := ByteArray.empty } =
      Except.ok { s with stack := tail }
    rw [← hs]

/-- EVM pure dynamic schedule, excluding memory expansion (charged separately). -/
def dynamicCost (fork : EVM.Fork) (s : SharedState .EVM) : Instruction → Nat
  | .binary .exp _ exponent => CexpPure exponent
  | .binary .mul .. | .binary .div .. | .binary .mod .. => Glow
  | .binary .. => Gverylow
  | .sload k => CsloadPure fork
      (s.substate.accessedStorageKeys.contains (s.executionEnv.codeOwner, k))
  | .tload _ => Ctload
  | .keccak _ size => Ckeccak256Pure size
  | .log0 _ size => ClogPure 0 size
  | .log1 _ size _ => ClogPure 1 size
  | .log2 _ size _ _ => ClogPure 2 size
  | .log3 _ size _ _ _ => ClogPure 3 size
  | .log4 _ size _ _ _ _ => ClogPure 4 size
  | .calldatacopy _ _ size | .mcopy _ _ size => CcopyPure size
  | .stop | .ret .. | .revert .. => Gzero

/-- Every requested instruction has exactly its EVM pure cost in Yul, for
    arbitrary forks, words, memory, warm/cold access sets and account contents. -/
theorem dynamic_gas_commutes (i : Instruction) (fork : EVM.Fork)
    (y : SharedState .Yul) (e : SharedState .EVM) (vs : Yul.VarStore)
    (h : Related y e) :
    Yul.yulPrimOpDynamicGas fork (.Ok y vs) (i.op .Yul) i.args =
      dynamicCost fork e i := by
  cases i with
  | binary b a c => cases b <;> rfl
  | sload k =>
    change CsloadPure fork (y.substate.accessedStorageKeys.contains
      (y.executionEnv.codeOwner, k)) = _
    rw [h.substate, h.owner]
    rfl
  | tload | keccak | log0 | log1 | log2 | log3 | log4
  | calldatacopy | mcopy | stop | ret | revert => rfl

/-- SSTORE is outside the shared-instruction set above, but its dynamic gas
    bridge also uses precisely the pure EVM original/current/new value rule. -/
theorem sstore_gas (fork : EVM.Fork) (s : Yul.State) (key value : UInt256) :
    Yul.yulPrimOpDynamicGas fork s .SSTORE [key, value] =
      CsstorePure fork
        (match s.toSharedState.σ₀.get? s.toSharedState.executionEnv.codeOwner with
          | none => ⟨0⟩ | some acc => acc.storage.getD key ⟨0⟩)
        (match s.toSharedState.accountMap.get? s.toSharedState.executionEnv.codeOwner with
          | none => ⟨0⟩ | some acc => acc.storage.getD key ⟨0⟩)
        value (s.toSharedState.substate.accessedStorageKeys.contains
          (s.toSharedState.executionEnv.codeOwner, key)) := by
  rfl

/-- The base and mid groups complement the verylow, low and zero groups in
    `dynamic_gas_commutes`. Both arities and all arguments are unrestricted. -/
theorem base_mid_gas (fork : EVM.Fork) (s : Yul.State) (operands : List UInt256) :
    Yul.yulPrimOpDynamicGas fork s .ADDRESS operands = Gbase ∧
    Yul.yulPrimOpDynamicGas fork s .ADDMOD operands = Gmid ∧
    Yul.yulPrimOpDynamicGas fork s .MULMOD operands = Gmid := by
  exact ⟨rfl, rfl, rfl⟩

/-- Combined certification: actual interpreter steps factor through the shared
    effects, and both result/state observations and dynamic gas commute.
    Yul halts/reverts are represented by `yulOutcome`, with no invented state
    recovery for REVERT. STOP requires its exact returnData compatibility condition. -/
theorem dialect_commutation (i : Instruction) (fork : EVM.Fork)
    (y : SharedState .Yul) (e : EVM.State) (vs : Yul.VarStore)
    (tail : List UInt256) (h : Related y e.toSharedState)
    (hstop : i = .stop → e.returnData = ByteArray.empty) :
    step (i.op .Yul) none (.Ok y vs) i.args = yulOutcome i y vs ∧
    step (i.op .EVM) none {e with stack := i.args ++ tail} =
      .ok (evmOutcome i {e with stack := i.args ++ tail} tail) ∧
    Related (effect i y).1 (effect i e.toSharedState).1 ∧
    (effect i y).2 = (effect i e.toSharedState).2 ∧
    Yul.yulPrimOpDynamicGas fork (.Ok y vs) (i.op .Yul) i.args =
      dynamicCost fork e.toSharedState i := by
  have he := effects_commute i y e.toSharedState h
  exact ⟨yul_step_effect i y vs, evm_step_effect i e tail hstop,
    he.1, he.2, dynamic_gas_commutes i fork y e.toSharedState vs h⟩

#print axioms dialect_commutation
#print axioms sstore_gas
#print axioms base_mid_gas

end EvmYul.MetaSpec.DialectCommutation
