# EVMYulLean 2.0 — Wave E3 & E4 Architectural Probe & Blueprint (`E3-probe-conform-eest-and-metaspecs`)

## 1. Multi-Fork Network Dispatch (`Shanghai`, `Cancun`, `Prague`, `Osaka`) & EEST Alignment

### Current State in `Conform/TestRunner.lean` & `Conform/Model.lean`
1. `Conform/TestRunner.lean` filters tests exclusively by `test.network.startsWith "Cancun"` and calls `EVM.intrinsicGas T` with the default `.Cancun` parameter.
2. `EvmYul/EVM/Gas.lean` defines `inductive Fork` (`Frontier .. Shanghai, Cancun, Prague, Osaka`) with `Fork.hasEIP2929` and `Fork.hasEIP7623`, and `intrinsicGas (T : Transaction) (fork : Fork := .Cancun)`.
3. `EvmYul/EVM/PragueOsakaSpecs.lean` defines EIP-7702 delegation indicators (`0xef0100 || addr`, `extractDelegationTarget?`, `encodeDelegationIndicator`), EIP-2537 BLS12-381 precompile gas schedules, EIP-2935 historical blockhash ring buffer (`8191`), EIP-7951 `P256VERIFY` (`6900` gas), and EIP-6780 same-transaction `SELFDESTRUCT` preservation.

### Target Multi-Fork Dispatch Blueprint (`EvmYul/Specs/ConformMultiFork.lean` & `Conform/TestRunner.lean`)
- **`Fork.ofNetworkString (net : String) : Option EVM.Fork`**:
  - Maps `"Shanghai"` prefix $\to$ `some .Shanghai`
  - Maps `"Cancun"` prefix $\to$ `some .Cancun`
  - Maps `"Prague"` prefix $\to$ `some .Prague`
  - Maps `"Osaka"` prefix $\to$ `some .Osaka`
- **Conservative Extension Theorem (`cancun_conservative`)**:
  - `ofNetworkString "Cancun" = some .Cancun` and `intrinsicGas tx .Cancun` preserves 100% of existing Cancun conformance behavior.
- **Prague/Osaka EIP-7623 Calldata Floor Dominance (`prague_intrinsicGas_ge_cancun`)**:
  - For all transactions `tx`, `EVM.intrinsicGas tx .Cancun ≤ EVM.intrinsicGas tx .Prague` and `EVM.intrinsicGas tx .Prague = EVM.intrinsicGas tx .Osaka`.
- **EIP-3529 Refund Cap (`effectiveGasRefund`)**:
  - `effectiveGasRefund gasUsed refundCounter = min refundCounter (gasUsed / 5) ≤ gasUsed / 5`, ensuring net gas charged is at least `gasUsed - gasUsed / 5`.

---

## 2. Blueprint for the 5 `EvmYul/MetaSpecs/` Modules & Wave E4 Bridges

| Module | Core Abstraction | Key Certified Theorems (`0 sorryAx`, `non_vacuous_and_tight`) |
| :--- | :--- | :--- |
| **`EvmYul/MetaSpecs/DialectCommutation.lean`** | Commutation of shared `Operation` semantics and dynamic gas between `.Yul` and `.EVM`. | `yul_evm_sload_gas_commutes`, `yul_evm_sstore_gas_commutes`, `yul_evm_keccak256_gas_commutes`, `yul_evm_exp_gas_commutes`, `yul_evm_copy_gas_commutes`, `yul_evm_log_gas_commutes`, `yul_evm_verylow_arith_gas_commutes`. |
| **`EvmYul/MetaSpecs/StateLensAlgebra.lean`** | Generic `StateLens (S K V : Type)` and `unchangedExcept` frame algebra over `AccountMap`, `StorageMap`, `TransientStorage`, `Memory`, and `Substate`. | `get_set_same`, `get_set_ne`, `set_set_same`, `unchangedExcept_refl`, `unchangedExcept_symm`, `unchangedExcept_trans`, `unchangedExcept_update_self`. |
| **`EvmYul/MetaSpecs/StaticCallAndRollback.lean`** | `STATICCALL` (`perm = false`) world-state immutability and atomic checkpoint restoration on `REVERT` vs exceptional halt. | `staticMode_forbids_mutation`, `prepareChildCallEnv_preserves_static_mode`, `revertRollback_restores_worldState`, `exceptionRollback_restores_worldState_and_burns_gas`, `revert_preserves_remaining_gas_minus_mem`. |
| **`EvmYul/MetaSpecs/GasTermination.lean`** | Lexicographic termination measure `evmTerminationMeasure (depth gasAvail : Nat) := (1024 - min depth 1024) * 2^64 + gasAvail`. | `consumeYulGas_strict_decrease`, `call_depth_component_strict_decrease`, `child_call_measure_strict_decrease`, `gas_63_64_cap_strict_decrease`, `gas_63_64_cap_le_self`. |
| **`EvmYul/Specs/ConformMultiFork.lean`** | Multi-fork network parser, EIP-7623 floor monotonic ordering, and EIP-3529 refund cap. | `ofNetworkString_shanghai`, `ofNetworkString_cancun`, `ofNetworkString_prague`, `ofNetworkString_osaka`, `effectiveGasRefund_le_fifth`, `prague_intrinsicGas_ge_cancun`. |
| **`EvmYul/Specs/YulEvmGasEquivalence.lean`** (Wave E4) | Total Yul step gas `yulStepTotalGas = yulPrimOpDynamicGas + yulMemoryExpansionGas` and sequential `consumeYulGas` composition for Verity `Compiler/Proofs/`. | `consumeYulGas_seq_ok_iff`, `consumeYulGas_seq_remaining`, `yulStepTotalGas_ge_dynamic`, `yulStepTotalGas_ge_memory`, `yulPrimOpDynamicGas_sload_eq`, `yulPrimOpDynamicGas_sstore_eq`, `yulPrimOpDynamicGas_keccak256_eq`. |
| **`EvmYul/Specs/MessageCallSimulation.lean`** (Wave E4) | 63/64 message-call gas forwarding `forwardedCallGas` and caller/child frame composition connecting `Yul.MessageCallCombinator` to `EVM.Gas.L`. | `forwardedCallGas_no_stipend_le_L`, `forwardedCallGas_staticCall_no_stipend`, `prepareChildCallEnv_depth_inc`, `prepareChildCallEnv_call_owner_and_sender`, `prepareChildCallEnv_staticCall_invariants`, `callerGasAfterChildReturn_le_avail`. |
