# EVMYulLean 2.0 — Yellow Paper, EELS, `evm-dafny`, KEVM & Isabelle/HOL4 Traceability Matrix

## 1. Scope & Purpose

This document provides the cross-specification traceability matrix for **`EVMYulLean 2.0`**, mapping every core Ethereum Yellow Paper equation and EIP semantic rule across:
1. **Ethereum Yellow Paper (YP)** — Formal mathematical equations `(43)`, `(63..68)`, `(120..155)`, `(326)`, `(328)`, `(331..339)`, Appendix G (Fee Schedule), and Appendix H (`C'`, `C_mem`, `Csstore`, `Csload`, `Ccall`, `Cselfdestruct`, `L`).
2. **Ethereum Execution Layer Specifications (EELS)** — Python reference implementation modules (`ethereum.cancun.vm`, `ethereum.prague.vm`, `ethereum.osaka.vm`).
3. **Consensys `evm-dafny`** — Total functional Dafny specification (`src/dafny/evm.dfy`, `src/dafny/gas.dfy`, `src/dafny/bytecode.dfy`).
4. **Runtime Verification `KEVM` (`evm-semantics`)** — K framework semantics (`evm.md`, `gas.md`, `serialization.md`).
5. **Isabelle/HOL4 (`lem` EVM)** — Lem/Isabelle formalization (`lem/evm.lem`).
6. **`EVMYulLean 2.0` Lean 4 Kernel Symbols** — Total, stack-safe, `Fork`-parameterized definitions and machine-checked theorems in `EvmYul/`.

---

## 2. Equation-by-Equation Cross-Specification Matrix

| YP Eq. / Appendix | Semantic Concept | EELS (`ethereum.<fork>.vm`) | `evm-dafny` | `KEVM` (`evm.md` / `gas.md`) | Isabelle / HOL4 (`evm.lem`) | `EVMYulLean 2.0` Symbol & Spec Theorem |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Eq. (43)** | Valid `JUMPDEST` set $D(c) = D_J(c, 0)$ skipping `PUSH1..PUSH32` immediate bytes | `runtime.get_valid_jump_destinations` | `Bytecode.ValidJumpDests` | `#computeValidJumpDests` | `compute_valid_jumpdests` | `EvmYul.EVM.D_J`, `EvmYul.EVM.D_J_total` (`EvmYul/EVM/JumpdestTotal.lean`) |
| **Eq. (63–65)** | Intrinsic gas $g_0(T)$ & EIP-3860 initcode word cost $R(x) = G_{\text{initcodeword}} \cdot \lceil x / 32 \rceil$ | `fork.calculate_intrinsic_cost` | `Gas.IntrinsicGas` | `#intrinsicGas` | `tx_intrinsic_gas` | `EvmYul.EVM.R`, `EvmYul.EVM.intrinsicGas` (`EvmYul/EVM/Gas.lean`), `yp_eq_65_initcode_word_bound` |
| **Eq. (66–68)** | Transaction execution precondition ($T_g \ge g_0$, nonce, up-front cost $v_0$) | `fork.validate_transaction` | `Tx.Validate` | `#validateTx` | `validate_tx` | `EvmYul.EVM.Execution.preCheck` (`EvmYul/EVM/Semantics.lean`) |
| **Eq. (120–155)** | Execution cycle $\Upsilon$, exceptional halting $Z(\sigma, \mu, A, I)$, normal halting $H(\mu, I)$ | `interpreter.process_message_call`, `evm_step` | `EVM.Execute`, `EVM.Step` | `<k> #execute ... </k>` | `program_sem`, `next_state` | `EvmYul.EVM.Ξ`, `EvmYul.EVM.Ψ`, `EvmYul.EVM.X`, `EvmYul.EVM.Z` (`EvmYul/EVM/Semantics.lean`) |
| **Eq. (326)** | Memory expansion function $M(s, f, l) = s \text{ if } l = 0 \text{ else } \max(s, \lceil (f + l)/32 \rceil)$ | `memory.calculate_memory_size` | `Memory.Expand` | `#memoryUsageUpdate` | `M_expansion` | `EvmYul.MachineState.M` (`EvmYul/MachineStateOps.lean`) |
| **Eq. (328)** | Memory gas cost $C_{\text{mem}}(a) = G_{\text{memory}} \cdot a + \lfloor a^2 / 512 \rfloor$ | `gas.calculate_memory_gas_cost` | `Gas.MemoryCost` | `Cmem(A)` | `C_mem` | `EvmYul.EVM.Cₘ` (`EvmYul/EVM/Gas.lean`), `yp_eq_328_memory_zero`, `yp_eq_328_memory_monotone` |
| **Eq. (331)** | EIP-150 all-but-one-64th cap $L(n) = n - \lfloor n / 64 \rfloor$ | `gas.max_message_call_gas` | `Gas.AllButOne64th` | `L(N)` (`allBut64th`) | `L_cap` | `EvmYul.EVM.L` (`EvmYul/EVM/Gas.lean`), `yp_eq_331_cap_le_self`, `yp_eq_331_cap_strict_lt` |
| **Eq. (332–335)** | EIP-2929 / EIP-2200 / EIP-3529 `SSTORE` cost $C_{\text{SSTORE}}(\sigma, \mu, A, I)$ & warm/cold `SLOAD` | `instructions.storage.sstore`, `sload` | `Gas.SstoreGas`, `Gas.SloadGas` | `Csstore`, `Csload` | `C_sstore` | `EvmYul.EVM.CsstorePure`, `EvmYul.EVM.CsloadPure` (`EvmYul/EVM/Gas.lean`) |
| **Eq. (336–339)** | Message call cost $C_{\text{CALL}}$, stipends $G_{\text{callstipend}}$, value transfer $G_{\text{callvalue}}$, new account $G_{\text{newaccount}}$ | `gas.calculate_message_call_gas` | `Gas.CallGas` | `Ccall`, `Ccallgas` | `C_call` | `EvmYul.EVM.Ccall`, `EvmYul.EVM.Ccallgas`, `EvmYul.EVM.Cextra` (`EvmYul/EVM/Gas.lean`) |
| **Appendix G** | Fee schedule constants ($G_{\text{zero}}, G_{\text{base}}, G_{\text{verylow}}, G_{\text{low}}, G_{\text{mid}}, G_{\text{high}}, \dots$) | `vm.gas.GasCosts` | `Gas.Constants` | `schedule.md` | `fee_schedule` | `GasConstants.*` (`EvmYul/EVM/GasConstants.lean`) |
| **Appendix H.1** | Third gas summand $C'(\sigma, \mu, A, I)$ + memory delta $C_{\text{mem}}(\mu'_i) - C_{\text{mem}}(\mu_i)$ | `interpreter.step_gas` | `Gas.StepGas` | `#gasExec` | `meter_gas` | `EvmYul.EVM.C'`, `EvmYul.EVM.memoryExpansionCost`, `EvmYul.EVM.memoryExpansionCostPure` |

---

## 3. Multi-Fork Evolution Matrix (`Shanghai` → `Cancun` → `Prague` → `Osaka`)

| Fork | Key EIPs | Formalization in `EVMYulLean 2.0` |
| :--- | :--- | :--- |
| **Shanghai** | **EIP-3651** (Warm `COINBASE`), **EIP-3855** (`PUSH0` in $W_{\text{base}}$), **EIP-3860** (Limit & meter initcode $R(x) = 2 \cdot \lceil x / 32 \rceil$, max $49152$ bytes) | `Operation.PUSH0 ∈ Wbase`, `EvmYul.EVM.R`, `maxInitcodeSize = 49152` (`EvmYul/Specs/YellowPaperTraceability.lean`) |
| **Cancun** | **EIP-1153** (`TLOAD`/`TSTORE` at $100$ gas), **EIP-4844** (`BLOBHASH` at $3$ gas, `BLOBBASEFEE` at $2$ gas), **EIP-5656** (`MCOPY` in $W_{\text{copy}}$), **EIP-6780** (`SELFDESTRUCT` only deletes in same-tx creation) | `Ctload`, `Ctstore`, `HASH_OPCODE_GAS`, `.MCOPY ∈ Wcopy`, `eip6780SelfdestructSpec` (`EvmYul/EVM/PragueOsakaSpecs.lean`) |
| **Prague (Pectra)** | **EIP-7702** (EOA code delegation designator `0xef0100 \|\| address`), **EIP-2537** (BLS12-381 precompiles `0x0b..0x11`), **EIP-2935** (Historical block hashes at `0x0000F90827F1C53a10cb7A02335B175320002935`, window `8191`), **EIP-7623** (Calldata floor gas $21000 + 10 \cdot \text{tokens}$) | `Fork.Prague`, `Fork.hasEIP7623`, `intrinsicGas` floor in `EvmYul/EVM/Gas.lean`, `EvmYul/EVM/PragueOsakaSpecs.lean` |
| **Osaka (Fusaka)** | **EIP-7951** (`P256VERIFY` precompile at `0x100`, cost `6900` gas), plus full Prague set | `Fork.Osaka`, `eip7951PrecompileAddress`, `eip7951P256VerifyGas` (`EvmYul/EVM/PragueOsakaSpecs.lean`) |

---

## 4. Architectural Probe Findings Resolved in Waves E1 & E2

1. **`UInt256` Internal Representation (`EvmYul/UInt256.lean`)**:
   - Migrated from `Fin UInt256.size` to `structure UInt256 where toBitVec : BitVec 256` with `@[inline, reducible] def val (a : UInt256) : Fin UInt256.size := a.toBitVec.toFin`.
   - Unlocks bit-blasting (`bv_decide`) via `UInt256.ext` (`EvmYul/Specs/UInt256BitVecBridge.lean`) while preserving all downstream `Fin`-based proofs.
2. **Elimination of Partial Indexing in `Gas.lean`**:
   - Replaced all 41 partial indexing sites (`s.stack[i]!`, `σ.get!`) in `EvmYul/EVM/Gas.lean` with total safe accessors (`μₛ[i]?.getD ⟨0⟩`, `σ.find?`) and pure typed operand functions (`CsstorePure`, `CsloadPure`, `CselfdestructPure`, `CexpPure`, `Ckeccak256Pure`, `CcopyPure`, `ClogPure`, `memoryExpansionCostPure`).
3. **Total `JUMPDEST` Analysis (`EvmYul/EVM/JumpdestTotal.lean`)**:
   - Provides a structurally recursive, fuel-bounded `D_J_total` with machine-checked step monotonicity (`nextPcAfterOp_gt`) and fuel bounds.
4. **Unified Yul Message Call Combinator (`EvmYul/Yul/MessageCallCombinator.lean`) & Yul Gas Accounting (`EvmYul/Yul/GasInterpreter.lean`)**:
   - Factors the 4 EVM/Yul call modes (`Call`, `CallCode`, `DelegateCall`, `StaticCall`) and bridges `.Yul` primitive operations to the total `EVM.Gas` cost model with `OutOfGas` halting guarantees.
