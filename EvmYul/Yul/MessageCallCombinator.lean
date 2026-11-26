import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.StateOps
import EvmYul.Wheels

namespace EvmYul.Yul

/-- The four modes of a Yul message call. -/
inductive YulCallMode where
  | Call
  | CallCode
  | DelegateCall
  | StaticCall
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Arguments shared by the message-call instructions, including their gas operand. -/
structure YulCallParams where
  gas : UInt256
  target : AccountAddress
  value : UInt256
  inOffset : UInt256
  inSize : UInt256
  outOffset : UInt256
  outSize : UInt256

/-- CALL and STATICCALL use the target's storage context. -/
def effectiveCodeOwner (mode : YulCallMode)
    (callerOwner target : AccountAddress) : AccountAddress :=
  match mode with
  | .Call | .StaticCall => target
  | .CallCode | .DelegateCall => callerOwner

/-- Delegation inherits the immediate caller (`source`, `CALLER`); other modes use the calling
contract (`codeOwner`). -/
def effectiveSender (mode : YulCallMode)
    (callerOwner callerSource : AccountAddress) : AccountAddress :=
  match mode with
  | .DelegateCall => callerSource
  | .Call | .CallCode | .StaticCall => callerOwner

/-- Delegation inherits value and static calls always carry zero value. -/
def effectiveWeiValue (mode : YulCallMode) (callVal envVal : UInt256) : UInt256 :=
  match mode with
  | .Call | .CallCode => callVal
  | .DelegateCall => envVal
  | .StaticCall => ⟨0⟩

/-- A child cannot regain write permission, and STATICCALL always removes it. -/
def effectivePerm (mode : YulCallMode) (callerPerm : Bool) : Bool :=
  match mode with
  | .StaticCall => false
  | .Call | .CallCode | .DelegateCall => callerPerm

/-- Prepare the mode-dependent child environment. Callee code is installed separately by the caller
after looking up `params.target`. `ExecutionEnv.sender` is the transaction origin (`ORIGIN`, Yellow
Paper `Iₒ`) and persists across all call modes; `ExecutionEnv.source` is the immediate caller
(`CALLER`, Yellow Paper `Iₛ`).

Departure from upstream: upstream overwrote `sender` via `effectiveSender`, causing nested calls
to change `ORIGIN`. -/
def prepareChildCallEnv (mode : YulCallMode) (parentEnv : ExecutionEnv .Yul)
    (params : YulCallParams) (calldata : ByteArray) : ExecutionEnv .Yul :=
  { parentEnv with
    codeOwner := effectiveCodeOwner mode parentEnv.codeOwner params.target
    source := effectiveSender mode parentEnv.codeOwner parentEnv.source
    weiValue := effectiveWeiValue mode params.value parentEnv.weiValue
    perm := effectivePerm mode parentEnv.perm
    calldata := calldata
    depth := parentEnv.depth + 1 }

/-- Restore the parent's execution environment after a child message call completes. -/
def restoreParentCallEnv (parentEnv childEnv : ExecutionEnv .Yul) : ExecutionEnv .Yul :=
  { childEnv with
    calldata := parentEnv.calldata
    code := parentEnv.code
    codeOwner := parentEnv.codeOwner
    sender := parentEnv.sender
    source := parentEnv.source
    weiValue := parentEnv.weiValue
    depth := parentEnv.depth
    perm := parentEnv.perm }

theorem restoreParentCallEnv_preserves_parent
    (parentEnv childEnv : ExecutionEnv .Yul) :
    let restored := restoreParentCallEnv parentEnv childEnv
    restored.calldata = parentEnv.calldata ∧
    restored.codeOwner = parentEnv.codeOwner ∧
    restored.sender = parentEnv.sender ∧
    restored.depth = parentEnv.depth ∧
    restored.perm = parentEnv.perm := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem effectivePerm_staticCall (p : Bool) : effectivePerm .StaticCall p = false := by
  rfl

theorem effectivePerm_preserves_false (mode : YulCallMode) :
    effectivePerm mode false = false := by
  cases mode <;> rfl

theorem prepareChildCallEnv_preserves_origin
    (mode : YulCallMode) (env : ExecutionEnv .Yul) (params : YulCallParams) (cd : ByteArray) :
    (prepareChildCallEnv mode env params cd).sender = env.sender := rfl

theorem delegateCall_preserves_codeOwner_and_sender
    (env : ExecutionEnv .Yul) (params : YulCallParams) (cd : ByteArray) :
    (prepareChildCallEnv .DelegateCall env params cd).codeOwner = env.codeOwner ∧
    (prepareChildCallEnv .DelegateCall env params cd).sender = env.sender ∧
    (prepareChildCallEnv .DelegateCall env params cd).source = env.source := by
  exact ⟨rfl, rfl, rfl⟩

example (cd : ByteArray) :
    let origin : AccountAddress := Fin.ofNat _ 10
    let caller : AccountAddress := Fin.ofNat _ 20
    let callee : AccountAddress := Fin.ofNat _ 30
    let parentEnv : ExecutionEnv .Yul :=
      { (default : ExecutionEnv .Yul) with
          sender := origin, source := origin, codeOwner := caller }
    let params : YulCallParams :=
      { gas := ⟨0⟩, target := callee, value := ⟨0⟩,
        inOffset := ⟨0⟩, inSize := ⟨0⟩, outOffset := ⟨0⟩, outSize := ⟨0⟩ }
    let child := prepareChildCallEnv .Call parentEnv params cd
    child.sender = origin ∧ child.source = caller ∧ child.codeOwner = callee :=
  ⟨rfl, rfl, rfl⟩

theorem staticCall_zero_weiValue (callVal envVal : UInt256) :
    effectiveWeiValue .StaticCall callVal envVal = ⟨0⟩ := by
  rfl

end EvmYul.Yul
