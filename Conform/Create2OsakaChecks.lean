import EvmYul.EVM.Semantics

/-! Runtime regression calibrated against Foundry v1.5.0 / Osaka. In
particular, EIP-7610 storage collision rules are not active on that fork. -/
namespace Conform.Create2OsakaChecks
open EvmYul

private def creator : AccountAddress := AccountAddress.ofUInt256 (.ofNat 8193)
private def target : AccountAddress := AccountAddress.ofUInt256
  (.ofNat 0xe317ec6689ba1293927261f8acda33b2db0bb1ba)
private def code : ByteArray := ⟨#[0x60,0x63,0x60,0x07,0x55,0x7f,
  0x60,0x0b,0x38,0x03,0x80,0x60,0x0b,0x5f,0x39,0x5f,0xf3,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0x5f,0x52,0x60,0x07,0x60,0x0b,0x5f,0x5f,0xf5,0x5f,0x52,0x60,0x20,0x5f,0xf3]⟩

private def initial (existing : Account .EVM) : EVM.State :=
  let owner := ({ (Inhabited.default : Account .EVM) with code := code }).updateStorage (.ofNat 7) (.ofNat 23)
  let accounts := (Inhabited.default : AccountMap .EVM).insert creator owner |>.insert target existing
  { (Inhabited.default : EVM.State) with
    accountMap := accounts
    σ₀ := accounts
    gasAvailable := .ofNat 1000000
    executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with
      codeOwner := creator, code := code, perm := true }
    substate := { (Inhabited.default : Substate) with
      accessedAccounts := (Inhabited.default : Substate).accessedAccounts.insert creator } }

private def execute (before : EVM.State) : IO (EVM.State × ByteArray) := do
  match EVM.X 80 (EVM.D_J code (.ofNat 0)) before with
  | .ok (.success after data) => pure (after, data)
  | _ => throw (IO.userError "native CREATE2 regression did not return successfully")

private def word (machine : EVM.State) (owner : AccountAddress) (slot : Nat) : UInt256 :=
  ((machine.accountMap.get? owner).getD default).storage.getD (.ofNat slot) (.ofNat 0)

private def account (machine : EVM.State) (owner : AccountAddress) : Account .EVM :=
  (machine.accountMap.get? owner).getD default

private def checkCreated (existing : Account .EVM) : IO Unit := do
  let (after, data) ← execute (initial existing)
  unless after.gasAvailable.toNat == 962934 && data == (UInt256.ofNat target.val).toByteArray &&
      (account after creator).nonce.toNat == 1 &&
      (account after target).nonce.toNat == 1 &&
      (account after target).balance == existing.balance &&
      ((after.σ₀.get? target).getD default).storage.getD (.ofNat 9) (.ofNat 0) ==
        existing.storage.getD (.ofNat 9) (.ofNat 0) &&
      (account after target).code.isEmpty &&
      word after target 9 == UInt256.ofNat 0 &&
      word after creator 7 == UInt256.ofNat 99 &&
      after.substate.accessedAccounts.contains target &&
      after.createdAccounts.contains target && after.substate.logSeries.isEmpty do
    throw (IO.userError "Osaka CREATE2 must accept storage-only target and clear its persistent storage")

private def checkCollision (existing : Account .EVM) : IO Unit := do
  let (after, data) ← execute (initial existing)
  unless after.gasAvailable.toNat == 15036 && data == (UInt256.ofNat 0).toByteArray &&
      (account after creator).nonce.toNat == 1 &&
      (account after target) == existing &&
      word after creator 7 == UInt256.ofNat 99 &&
      after.substate.accessedAccounts.contains target &&
      !(after.createdAccounts.contains target) && after.substate.logSeries.isEmpty do
    throw (IO.userError "Osaka CREATE2 nonce/code collision must preserve the target snapshot")

def runChecks : IO Unit := do
  let existing := ({ (Inhabited.default : Account .EVM) with balance := .ofNat 19 }).updateStorage (.ofNat 9) (.ofNat 77)
  checkCreated existing
  checkCreated { existing with storage := default }
  checkCollision { existing with nonce := .ofNat 1 }
  checkCollision { existing with code := ⟨#[0x00]⟩ }
  IO.println "Osaka CREATE2 storage reset and nonce/code collision checks passed:4"

end Conform.Create2OsakaChecks

def main : IO Unit := Conform.Create2OsakaChecks.runChecks
