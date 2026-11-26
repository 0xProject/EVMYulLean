import EvmYul.Yul.GasInterpreter
import EvmYul.EVM.Gas
import EvmYul.Specs.GasSpec
import EvmYul.Specs.UInt256BitVecBridge

namespace EvmYul

namespace Specs

open EvmYul.EVM EvmYul.Yul GasConstants

/-- Total Yul step gas: Yellow Paper dynamic opcode cost plus memory-expansion delta. -/
def yulStepTotalGas (fork : EVM.Fork) (s : Yul.State) (op : Operation .Yul) (args : List UInt256) : ℕ :=
  yulPrimOpDynamicGas fork s op args + yulMemoryExpansionGas s op args

private theorem except_bind_error {α β : Type} (e : Yul.Exception) (f : α → Except Yul.Exception β) :
    (do let x ← (.error e : Except Yul.Exception α); f x) = .error e := by
  simp [bind, Except.bind]

/-- `consumeYulGas` on an `Ok` state replaces only `gasAvailable`. -/
private theorem consumeYulGas_ok (shared : EvmYul.SharedState .Yul) (store : VarStore) (cost : ℕ)
    (h : cost ≤ shared.toMachineState.gasAvailable.toNat) :
    consumeYulGas (.Ok shared store) cost =
      .ok (.Ok { shared with toMachineState :=
        { shared.toMachineState with
          gasAvailable := UInt256.ofNat (shared.toMachineState.gasAvailable.toNat - cost) } }
        store) := by
  unfold consumeYulGas
  simp [Yul.State.toMachineState, Yul.State.setMachineState, h]

/-- Sequential Yul gas consumption on an `Ok` state succeeds iff `c1 + c2 ≤ avail`,
    and then leaves `avail - (c1 + c2)`, provided the initial availability fits in a word.
    (`setMachineState` is the identity on `Checkpoint` / `OutOfFuel`, so those states
    cannot record a deducted balance.) -/
theorem consumeYulGas_seq_iff (shared : EvmYul.SharedState .Yul) (store : VarStore) (c1 c2 : ℕ)
    (havail : shared.toMachineState.gasAvailable.toNat < UInt256.size) :
    (do
        let s1 ← consumeYulGas (.Ok shared store) c1
        consumeYulGas s1 c2) =
      (if c1 + c2 ≤ shared.toMachineState.gasAvailable.toNat then
        .ok (Yul.State.setMachineState
          { shared.toMachineState with
            gasAvailable :=
              UInt256.ofNat (shared.toMachineState.gasAvailable.toNat - (c1 + c2)) }
          (.Ok shared store))
      else
        .error .OutOfFuel) := by
  set avail := shared.toMachineState.gasAvailable.toNat with hav
  have havail' : avail < UInt256.size := by simpa [hav] using havail
  by_cases h1 : c1 ≤ avail
  · have hgas : (UInt256.ofNat (avail - c1)).toNat = avail - c1 := by
      rw [UInt256.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) havail'
    have h1' : c1 ≤ shared.toMachineState.gasAvailable.toNat := by simpa [hav] using h1
    rw [consumeYulGas_ok shared store c1 h1']
    simp only [bind, Except.bind]
    by_cases h2 : c2 ≤ avail - c1
    · have hsum : c1 + c2 ≤ avail := by omega
      have hsub : (avail - c1) - c2 = avail - (c1 + c2) := by omega
      have h2' : c2 ≤ (UInt256.ofNat (shared.toMachineState.gasAvailable.toNat - c1)).toNat := by
        rw [← hav, hgas]; exact h2
      rw [consumeYulGas_ok _ store c2 h2']
      simp only [Yul.State.setMachineState, hav]
      rw [hgas, hsub]
      rw [ite_eq_left hsum]
    · have hsum : ¬ c1 + c2 ≤ avail := by omega
      have h2' : ¬ c2 ≤ (UInt256.ofNat (shared.toMachineState.gasAvailable.toNat - c1)).toNat := by
        rw [← hav, hgas]; exact h2
      have herr : consumeYulGas
          (.Ok
            { toState := shared.toState
              gasAvailable := UInt256.ofNat (shared.toMachineState.gasAvailable.toNat - c1)
              activeWords := shared.toMachineState.activeWords
              memory := shared.toMachineState.memory
              returnData := shared.toMachineState.returnData
              H_return := shared.toMachineState.H_return }
            store) c2 = .error .OutOfFuel := by
        unfold consumeYulGas
        dsimp [Yul.State.toMachineState]
        rw [ite_eq_right h2']
      rw [herr]
      split
      · rename_i hbad; exact absurd hbad hsum
      · rfl
  · have hsum : ¬ c1 + c2 ≤ avail := by omega
    have h1' : ¬ c1 ≤ shared.toMachineState.gasAvailable.toNat := by simpa [hav] using h1
    conv_lhs =>
      arg 1
      rw [show consumeYulGas (.Ok shared store) c1 = .error .OutOfFuel by
            unfold consumeYulGas
            dsimp [Yul.State.toMachineState]
            rw [ite_eq_right h1']]
    rw [except_bind_error]
    simp [hsum]

/-- Yul `KECCAK256` dynamic gas is the Yellow Paper `Ckeccak256Pure` of the size operand. -/
theorem yulPrimOpDynamicGas_keccak256_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .KECCAK256 args = Ckeccak256Pure (args[1]?.getD (0 : UInt256)) := by
  unfold yulPrimOpDynamicGas
  rfl

/-- Yul `SLOAD` dynamic gas is `CsloadPure` of the EIP-2929 warm bit of the slot operand. -/
theorem yulPrimOpDynamicGas_sload_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .SLOAD args =
      CsloadPure fork
        ((s.toSharedState.substate.accessedStorageKeys.contains
          (s.toSharedState.executionEnv.codeOwner, args[0]?.getD (0 : UInt256)))) := by
  unfold yulPrimOpDynamicGas
  rfl

/-- Yul `SSTORE` dynamic gas is `CsstorePure` of the original value, current value,
    written value, and EIP-2929 warm bit. -/
theorem yulPrimOpDynamicGas_sstore_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .SSTORE args =
      CsstorePure fork
        (match s.toSharedState.σ₀.get? s.toSharedState.executionEnv.codeOwner with
          | none => (0 : UInt256)
          | some acc => acc.storage.getD (args[0]?.getD (0 : UInt256)) (0 : UInt256))
        (match s.toSharedState.accountMap.get? s.toSharedState.executionEnv.codeOwner with
          | none => (0 : UInt256)
          | some acc => acc.storage.getD (args[0]?.getD (0 : UInt256)) (0 : UInt256))
        (args[1]?.getD (0 : UInt256))
        (s.toSharedState.substate.accessedStorageKeys.contains
          (s.toSharedState.executionEnv.codeOwner, args[0]?.getD (0 : UInt256))) := by
  unfold yulPrimOpDynamicGas
  rfl

theorem yulPrimOpDynamicGas_log0_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .LOG0 args = ClogPure 0 (args[1]?.getD (0 : UInt256)) := rfl

theorem yulPrimOpDynamicGas_log1_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .LOG1 args = ClogPure 1 (args[1]?.getD (0 : UInt256)) := rfl

theorem yulPrimOpDynamicGas_log2_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .LOG2 args = ClogPure 2 (args[1]?.getD (0 : UInt256)) := rfl

theorem yulPrimOpDynamicGas_log3_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .LOG3 args = ClogPure 3 (args[1]?.getD (0 : UInt256)) := rfl

theorem yulPrimOpDynamicGas_log4_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulPrimOpDynamicGas fork s .LOG4 args = ClogPure 4 (args[1]?.getD (0 : UInt256)) := rfl

theorem yulPrimOpDynamicGas_log_eq (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) (n : ℕ)
    (hn : n < 5) :
    yulPrimOpDynamicGas fork s
        ([.LOG0, .LOG1, .LOG2, .LOG3, .LOG4][n]'(Nat.lt_of_lt_of_le hn (by decide))) args =
      ClogPure n (args[1]?.getD (0 : UInt256)) := by
  match n, hn with
  | 0, _ => exact yulPrimOpDynamicGas_log0_eq fork s args
  | 1, _ => exact yulPrimOpDynamicGas_log1_eq fork s args
  | 2, _ => exact yulPrimOpDynamicGas_log2_eq fork s args
  | 3, _ => exact yulPrimOpDynamicGas_log3_eq fork s args
  | 4, _ => exact yulPrimOpDynamicGas_log4_eq fork s args

/-- A Yul step costs at least the Yellow Paper dynamic opcode component. -/
theorem yulStepTotalGas_ge_dynamic (fork : EVM.Fork) (s : Yul.State) (op : Operation .Yul)
    (args : List UInt256) :
    yulPrimOpDynamicGas fork s op args ≤ yulStepTotalGas fork s op args :=
  Nat.le_add_right _ _

/-- A Yul step costs at least the memory expansion component. -/
theorem yulStepTotalGas_ge_memory (fork : EVM.Fork) (s : Yul.State) (op : Operation .Yul)
    (args : List UInt256) :
    yulMemoryExpansionGas s op args ≤ yulStepTotalGas fork s op args :=
  Nat.le_add_left _ _

/-- Pure control-flow `STOP` incurs the empty-region memory expansion schedule. -/
theorem yulMemoryExpansionGas_stop_eq (s : Yul.State) (args : List UInt256) :
    yulMemoryExpansionGas s .STOP args =
      memoryExpansionCostPure s.toMachineState.activeWords [] :=
  rfl

/-- Adding a memory delta never decreases total step gas. -/
theorem yulStepTotalGas_mono_memory {fork : EVM.Fork} {s : Yul.State} {op : Operation .Yul}
    {args : List UInt256} (extra : ℕ) :
    yulStepTotalGas fork s op args ≤ yulStepTotalGas fork s op args + extra :=
  Nat.le_add_right _ _

/-- `KECCAK256` total step gas is monotone in the hashed byte length. -/
theorem yulStepTotalGas_keccak256_monotone {fork : EVM.Fork} {s : Yul.State}
    {args₁ args₂ : List UInt256}
    (h : (args₁[1]?.getD (0 : UInt256)).toNat ≤ (args₂[1]?.getD (0 : UInt256)).toNat)
    (hmem : yulMemoryExpansionGas s .KECCAK256 args₁ ≤ yulMemoryExpansionGas s .KECCAK256 args₂) :
    yulStepTotalGas fork s .KECCAK256 args₁ ≤ yulStepTotalGas fork s .KECCAK256 args₂ := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_keccak256_eq, yulPrimOpDynamicGas_keccak256_eq]
  exact Nat.add_le_add (ckeccak256Pure_monotone h) hmem

/-- `LOGn` total step gas is monotone in the topic count, at fixed memory delta. -/
private theorem yulMemoryExpansionGas_log_eq (s : Yul.State) (args : List UInt256) :
    yulMemoryExpansionGas s .LOG0 args = yulMemoryExpansionGas s .LOG1 args ∧
    yulMemoryExpansionGas s .LOG1 args = yulMemoryExpansionGas s .LOG2 args ∧
    yulMemoryExpansionGas s .LOG2 args = yulMemoryExpansionGas s .LOG3 args ∧
    yulMemoryExpansionGas s .LOG3 args = yulMemoryExpansionGas s .LOG4 args := by
  unfold yulMemoryExpansionGas
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem yulStepTotalGas_log01_le (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulStepTotalGas fork s .LOG0 args ≤ yulStepTotalGas fork s .LOG1 args := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_log0_eq, yulPrimOpDynamicGas_log1_eq,
      (yulMemoryExpansionGas_log_eq s args).1]
  exact Nat.add_le_add_right (clogPure_topic_monotone _ (by decide)) _

theorem yulStepTotalGas_log12_le (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulStepTotalGas fork s .LOG1 args ≤ yulStepTotalGas fork s .LOG2 args := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_log1_eq, yulPrimOpDynamicGas_log2_eq,
      (yulMemoryExpansionGas_log_eq s args).2.1]
  exact Nat.add_le_add_right (clogPure_topic_monotone _ (by decide)) _

theorem yulStepTotalGas_log23_le (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulStepTotalGas fork s .LOG2 args ≤ yulStepTotalGas fork s .LOG3 args := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_log2_eq, yulPrimOpDynamicGas_log3_eq,
      (yulMemoryExpansionGas_log_eq s args).2.2.1]
  exact Nat.add_le_add_right (clogPure_topic_monotone _ (by decide)) _

theorem yulStepTotalGas_log34_le (fork : EVM.Fork) (s : Yul.State) (args : List UInt256) :
    yulStepTotalGas fork s .LOG3 args ≤ yulStepTotalGas fork s .LOG4 args := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_log3_eq, yulPrimOpDynamicGas_log4_eq,
      (yulMemoryExpansionGas_log_eq s args).2.2.2]
  exact Nat.add_le_add_right (clogPure_topic_monotone _ (by decide)) _

theorem yulStepTotalGas_log_topic_monotone (fork : EVM.Fork) (s : Yul.State) (args : List UInt256)
    {n : ℕ} (hn : n < 4) :
    yulStepTotalGas fork s ([.LOG0, .LOG1, .LOG2, .LOG3, .LOG4][n]'(Nat.lt_trans hn (by decide))) args ≤
      yulStepTotalGas fork s
        ([.LOG0, .LOG1, .LOG2, .LOG3, .LOG4][n + 1]'(Nat.succ_lt_succ hn)) args := by
  match n, hn with
  | 0, _ => exact yulStepTotalGas_log01_le fork s args
  | 1, _ => exact yulStepTotalGas_log12_le fork s args
  | 2, _ => exact yulStepTotalGas_log23_le fork s args
  | 3, _ => exact yulStepTotalGas_log34_le fork s args

/-- Warm `SLOAD` never costs more than cold `SLOAD`, including the zero memory delta. -/
theorem yulStepTotalGas_sload_warm_le_cold (fork : EVM.Fork) (sWarm sCold : Yul.State)
    (args : List UInt256)
    (hw : sWarm.toSharedState.substate.accessedStorageKeys.contains
        (sWarm.toSharedState.executionEnv.codeOwner, args[0]?.getD (0 : UInt256)) = true)
    (hc : sCold.toSharedState.substate.accessedStorageKeys.contains
        (sCold.toSharedState.executionEnv.codeOwner, args[0]?.getD (0 : UInt256)) = false)
    (hmem : yulMemoryExpansionGas sWarm .SLOAD args ≤ yulMemoryExpansionGas sCold .SLOAD args) :
    yulStepTotalGas fork sWarm .SLOAD args ≤ yulStepTotalGas fork sCold .SLOAD args := by
  unfold yulStepTotalGas
  rw [yulPrimOpDynamicGas_sload_eq, yulPrimOpDynamicGas_sload_eq, hw, hc]
  exact Nat.add_le_add (csloadPure_warm_le_cold fork) hmem

end Specs

end EvmYul
