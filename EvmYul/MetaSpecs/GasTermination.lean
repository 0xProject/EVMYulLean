import EvmYul.EVM.Gas
import EvmYul.Specs.GasSpec
import EvmYul.Yul.GasInterpreter

/-!
# Meta-Specification: Gas Monotonicity and Lexicographic Termination (`E3`)

Formalizes `MetaSpec.GasMonotonicityAndTermination` for `EVMYulLean 2.0`:
1. The lexicographic call-depth and gas termination measure
   `evmTerminationMeasure (depth gasAvail : Nat) : Nat := (1024 - min depth 1024) * (2 ^ 64) + gasAvail`.
2. Strict decrease of `gasAvailable` under `consumeYulGas` whenever `0 < cost`
   and `consumeYulGas s cost = .ok s'`.
3. Strict decrease of the call-depth component `1024 - (depth + 1) < 1024 - depth`
   (and `1024 - min (depth + 1) 1024 < 1024 - min depth 1024`) for `depth < 1024`.
4. EIP-150 message-call gas cap bounds `L(g) < g` for `64 ≤ g` and `L(g) ≤ g` for all `g`,
   establishing fuel-sufficiency for bounded gas execution.
-/

namespace EvmYul

namespace MetaSpec

open EvmYul.EVM
open EvmYul.Yul

/-- EVM maximum message-call stack depth limit (`1024`). -/
def maxCallDepth : Nat := 1024

/-- Lexicographic call-and-gas termination measure for bounded EVM/Yul execution:
    weights remaining call-depth capacity `1024 - min depth 1024` by `2 ^ 64`
    and adds the current frame's available gas `gasAvail`. -/
def evmTerminationMeasure (depth gasAvail : Nat) : Nat :=
  (1024 - min depth 1024) * (2 ^ 64) + gasAvail

/-- Theorem 1: Exact gas accounting under `consumeYulGas` on an active Yul state
    `Yul.State.Ok shared store`: succeeding with `.ok s'` guarantees
    `cost ≤ gasAvailable.toNat` and deducts `cost` from `gasAvailable.toNat`. -/
theorem consumeYulGas_ok_gasAvailable_eq
    (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat)
    (hStep : consumeYulGas (.Ok shared store) cost = .ok s') :
    cost ≤ (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat ∧
    s'.toMachineState.gasAvailable.toNat =
      (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat - cost := by
  unfold consumeYulGas at hStep
  dsimp at hStep
  split_ifs at hStep with hLe
  · cases hStep
    refine ⟨hLe, ?_⟩
    change (BitVec.ofNat 256 (shared.toMachineState.gasAvailable.toBitVec.toNat - cost)).toNat =
      shared.toMachineState.gasAvailable.toBitVec.toNat - cost
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) shared.toMachineState.gasAvailable.toBitVec.isLt)

/-- Theorem 2: Strict decrease of `gasAvailable.toNat` under `consumeYulGas` whenever
    `0 < cost` and `consumeYulGas (.Ok shared store) cost = .ok s'`. -/
theorem consumeYulGas_strict_decrease
    (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat)
    (hPos : 0 < cost)
    (hStep : consumeYulGas (.Ok shared store) cost = .ok s') :
    s'.toMachineState.gasAvailable.toNat <
      (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat := by
  obtain ⟨hLe, hEq⟩ := consumeYulGas_ok_gasAvailable_eq shared store s' cost hStep
  omega

/-- Theorem 3: Strict decrease of `gasAvailable` in the `UInt256` order (`<`) under
    `consumeYulGas` whenever `0 < cost` and `consumeYulGas (.Ok shared store) cost = .ok s'`. -/
theorem consumeYulGas_gasAvailable_lt
    (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat)
    (hPos : 0 < cost)
    (hStep : consumeYulGas (.Ok shared store) cost = .ok s') :
    s'.toMachineState.gasAvailable <
      (Yul.State.Ok shared store).toMachineState.gasAvailable := by
  have hNatLt := consumeYulGas_strict_decrease shared store s' cost hPos hStep
  exact hNatLt

/-- Theorem 4: Strict decrease of the call-depth component `1024 - (depth + 1) < 1024 - depth`
    and its clamped form `1024 - min (depth + 1) 1024 < 1024 - min depth 1024` for `depth < 1024`. -/
theorem callDepth_component_strict_decrease {depth : Nat} (hDepth : depth < 1024) :
    1024 - (depth + 1) < 1024 - depth ∧
    1024 - min (depth + 1) 1024 < 1024 - min depth 1024 := by
  omega

/-- Theorem 5: EIP-150 message-call gas cap `L(g) = g - g / 64` satisfies `L(g) ≤ g` for all `g`,
    strictly decreases `L(g) < g` whenever `64 ≤ g`, and is the identity `L(g) = g` for `g < 64`. -/
theorem eip150_L_fuel_sufficiency (g : Nat) :
    L g ≤ g ∧ (64 ≤ g → L g < g) ∧ (g < 64 → L g = g) := by
  refine ⟨L_le_self g, fun hGe => L_lt_self_of_ge_64 hGe, ?_⟩
  intro hLt
  unfold L
  omega

/-- Theorem 6: Intra-frame strict order characterization of `evmTerminationMeasure`: at any fixed
    call `depth`, the termination measure strictly decreases if and only if available gas
    strictly decreases (`gasAvail' < gasAvail`). -/
theorem evmTerminationMeasure_gas_lt_iff
    (depth gasAvail' gasAvail : Nat) :
    evmTerminationMeasure depth gasAvail' < evmTerminationMeasure depth gasAvail ↔
      gasAvail' < gasAvail := by
  unfold evmTerminationMeasure
  omega

/-- Theorem 7: Any positive-cost `consumeYulGas` transition on an active Yul state
    strictly decreases the lexicographic termination measure `evmTerminationMeasure` at fixed `depth`. -/
theorem evmTerminationMeasure_consumeYulGas_lt
    (depth : Nat) (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat)
    (hPos : 0 < cost)
    (hStep : consumeYulGas (.Ok shared store) cost = .ok s') :
    evmTerminationMeasure depth s'.toMachineState.gasAvailable.toNat <
      evmTerminationMeasure depth (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat := by
  rw [evmTerminationMeasure_gas_lt_iff]
  exact consumeYulGas_strict_decrease shared store s' cost hPos hStep

/-- Theorem 8: Cross-frame strict decrease of `evmTerminationMeasure`: entering a child call frame
    (`depth → depth + 1`) with `depth < 1024` and `childGas < 2 ^ 64` strictly decreases
    `evmTerminationMeasure`, even if `childGas` includes the `Gcallstipend = 2300` stipend. -/
theorem evmTerminationMeasure_childCall_lt
    {depth parentGas childGas : Nat}
    (hDepth : depth < 1024)
    (hChildBounded : childGas < 2 ^ 64) :
    evmTerminationMeasure (depth + 1) childGas < evmTerminationMeasure depth parentGas := by
  unfold evmTerminationMeasure
  omega

/-- Theorem 9: EIP-150 message-call gas cap `Cgascap` never exceeds the post-extra remaining gas
    `μ.gasAvailable.toNat - Cextra t r val σ A` when `Cextra ≤ μ.gasAvailable.toNat`, and is
    strictly smaller whenever at least `64` gas remains after `Cextra`. -/
theorem cgascap_bounded_by_remaining_gas
    (t r : AccountAddress) (val g : UInt256)
    (σ : AccountMap .EVM) (μ : MachineState) (A : Substate)
    (hExtra : Cextra t r val σ A ≤ μ.gasAvailable.toNat) :
    Cgascap t r val g σ μ A ≤ μ.gasAvailable.toNat - Cextra t r val σ A ∧
    (64 ≤ μ.gasAvailable.toNat - Cextra t r val σ A →
      Cgascap t r val g σ μ A < μ.gasAvailable.toNat - Cextra t r val σ A) := by
  unfold Cgascap
  rw [ite_eq_left hExtra]
  have hL_le : L (μ.gasAvailable.toNat - Cextra t r val σ A) ≤
      μ.gasAvailable.toNat - Cextra t r val σ A := L_le_self _
  refine ⟨Nat.le_trans (Nat.min_le_left _ _) hL_le, ?_⟩
  intro hGe64
  have hL_lt : L (μ.gasAvailable.toNat - Cextra t r val σ A) <
      μ.gasAvailable.toNat - Cextra t r val σ A := L_lt_self_of_ge_64 hGe64
  exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hL_lt

/-- `MetaSpec.GasMonotonicityAndTermination`:
    Bundled meta-specification of gas monotonicity, call-depth decrease, EIP-150 63/64ths
    fuel contraction, and lexicographic termination measure decrease. -/
structure GasMonotonicityAndTermination : Prop where
  measure_def :
    ∀ depth gasAvail : Nat,
      evmTerminationMeasure depth gasAvail = (1024 - min depth 1024) * (2 ^ 64) + gasAvail
  consume_strict_decrease :
    ∀ (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat),
      0 < cost →
      consumeYulGas (.Ok shared store) cost = .ok s' →
      s'.toMachineState.gasAvailable.toNat <
        (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat
  depth_strict_decrease :
    ∀ depth : Nat, depth < 1024 → 1024 - (depth + 1) < 1024 - depth
  eip150_cap_strict :
    ∀ g : Nat, 64 ≤ g → L g < g
  eip150_cap_le :
    ∀ g : Nat, L g ≤ g
  lexicographic_step_decrease :
    ∀ (depth : Nat) (shared : SharedState .Yul) (store : Yul.VarStore) (s' : Yul.State) (cost : Nat),
      0 < cost →
      consumeYulGas (.Ok shared store) cost = .ok s' →
      evmTerminationMeasure depth s'.toMachineState.gasAvailable.toNat <
        evmTerminationMeasure depth (Yul.State.Ok shared store).toMachineState.gasAvailable.toNat
  lexicographic_call_decrease :
    ∀ depth parentGas childGas : Nat,
      depth < 1024 →
      childGas < 2 ^ 64 →
      evmTerminationMeasure (depth + 1) childGas < evmTerminationMeasure depth parentGas

/-- Theorem 10: Master certification theorem establishing `MetaSpec.GasMonotonicityAndTermination`. -/
theorem gasMonotonicityAndTermination_holds : GasMonotonicityAndTermination where
  measure_def := fun _ _ => rfl
  consume_strict_decrease := consumeYulGas_strict_decrease
  depth_strict_decrease := fun _ h => (callDepth_component_strict_decrease h).1
  eip150_cap_strict := fun _ h => L_lt_self_of_ge_64 h
  eip150_cap_le := L_le_self
  lexicographic_step_decrease := evmTerminationMeasure_consumeYulGas_lt
  lexicographic_call_decrease := fun _ _ _ hD hC => evmTerminationMeasure_childCall_lt hD hC

/-- Theorem 11: For any `s s' : Yul.State` in the active `.Ok` state (`s = .Ok s.sharedState s.store`),
    consuming positive gas (`0 < cost`) with `consumeYulGas s cost = .ok s'` strictly decreases
    `gasAvailable.toNat`. -/
theorem consumeYulGas_state_strict_decrease
    (s s' : Yul.State) (cost : Nat)
    (hOk : s = .Ok s.sharedState s.store)
    (hPos : 0 < cost)
    (hStep : consumeYulGas s cost = .ok s') :
    s'.toMachineState.gasAvailable.toNat < s.toMachineState.gasAvailable.toNat := by
  rw [hOk] at hStep ⊢
  exact consumeYulGas_strict_decrease s.sharedState s.store s' cost hPos hStep

end MetaSpec

end EvmYul
