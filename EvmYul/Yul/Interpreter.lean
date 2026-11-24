import Mathlib.Data.Finmap

import EvmYul.Yul.Ast
import EvmYul.Yul.State
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps
import EvmYul.Yul.SizeLemmas
import EvmYul.Yul.Exception
import EvmYul.Yul.MessageCallCombinator
import EvmYul.Yul.GasInterpreter

import EvmYul.Semantics

set_option maxHeartbeats 400000 -- Needs more than 200000

namespace EvmYul

namespace Yul

open Ast SizeLemmas

-- ============================================================================
--  INTERPRETER
-- ============================================================================

def head' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
  | .ok (s, rets) => .ok (s, List.head! rets)
  | .error e => .error e

def cons' (arg : Literal) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, arg :: args)
  | .error e => .error e

def reverse' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, args.reverse)
  | .error e => .error e

def multifill' (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
  | .ok (s, rets) => .ok (s.multifill vars rets)
  | .error e => .error e

def setStatic (s : State) (p : Bool) : State :=
  match s with
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint j => .Checkpoint j
  | .Ok sharedState varstore =>
    let executionEnvStatic := { sharedState.executionEnv with
                                perm := p
                              }
    let sharedState' := { sharedState with
                          executionEnv := executionEnvStatic
                        }
    .Ok sharedState' varstore

def buildContractCallEmptyReturnState (s₀ : State) (accountMap₁ : Option (AccountMap .Yul)) (v : Literal) : Except Yul.Exception (State × List Literal) :=
    match s₀ with
    | .OutOfFuel => .error .OutOfFuel
    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
    | .Ok sharedState₀ varstore =>
      let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty,
                                             returnData := ByteArray.empty,
                                             accountMap := accountMap₁.getD s₀.toSharedState.accountMap }
      .ok (.Ok sharedState₁ varstore, [v])

/-- Restore the parent frame's execution environment and copy the bounded return-data slice
    after a child message call completes with `s₂`. -/
def finishChildCallSuccess
    (s₀ s₂ : State) (varstore : VarStore) (outOffset outSize : UInt256) :
    Except Yul.Exception (State × List Literal) :=
  let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
  match s₂ with
  | .OutOfFuel => .error .OutOfFuel
  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
  | .Ok sharedState₂ _ =>
    let executionEnv₃ := restoreParentCallEnv s₀.executionEnv sharedState₂.executionEnv
    let sharedState₃ := { sharedState₂ with
                            memory := memory₃,
                            returnData := s₂.toMachineState.H_return,
                            H_return := ByteArray.empty,
                            executionEnv := executionEnv₃ }
    .ok (.Ok sharedState₃ varstore, [⟨1⟩])

/-- A child message call that reverted with `data`: the world state rolls back to `s₀`, and,
    as for any call output (EIP-140, EIP-211), `data` is copied to the parent's
    `memory[outOffset, outOffset + min(outSize, ‖data‖))` and becomes its returndata. Returns `0`. -/
def finishChildCallRevert (s₀ : State) (outOffset outSize : UInt256) (data : ByteArray) :
    Except Yul.Exception (State × List Literal) :=
  match s₀ with
  | .OutOfFuel => .error .OutOfFuel
  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
  | .Ok sharedState₀ varstore =>
    let memory₁ := data.copySlice 0 sharedState₀.memory outOffset.toNat (min outSize.toNat data.size)
    .ok (.Ok { sharedState₀ with memory := memory₁, H_return := ByteArray.empty, returnData := data }
      varstore, [⟨0⟩])

/-- Unified child message-call outcome handler across `.CALL`, `.STATICCALL`, `.CALLCODE`, and `.DELEGATECALL`:
    - normal completion or `.YulHalt` restores parent environment via `finishChildCallSuccess` and returns `1`,
    - child `.Revert data` rolls back world state to `s₀`, exposes `data` via `finishChildCallRevert`, and returns `0`,
    - child `.StaticModeViolation` rolls back world state to `s₀`, with empty returndata, and returns `0`. -/
def finishChildCallOutcome {α : Type}
    (s₀ : State) (varstore : VarStore) (outOffset outSize : UInt256)
    (res : Except Yul.Exception (State × α)) :
    Except Yul.Exception (State × List Literal) :=
  match res with
  | .error (.YulHalt s₂ _) | .ok (s₂, _) =>
    finishChildCallSuccess s₀ s₂ varstore outOffset outSize
  | .error (.Revert data) =>
    finishChildCallRevert s₀ outOffset outSize data
  | .error .StaticModeViolation =>
    buildContractCallEmptyReturnState s₀ .none ⟨0⟩
  | .error e => .error e

mutual

def primCall (fuel : ℕ) (s₀ : State) (prim : Operation .Yul) (args : List Literal) : Except Yul.Exception (State × List Literal) :=
  do
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel₁ => 
      if ¬s₀.executionEnv.perm ∧ prim ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] then throw .StaticModeViolation
      match prim with
      | .CALL =>
        match args with
          | gas_arg :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner address value)
            match accountMap₁Opt with
              | .none =>
                buildContractCallEmptyReturnState s₀ .none ⟨0⟩
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024 then
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.get? address with
                        | .none =>
                          buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩
                        | .some yulContract =>
                          let callParams : YulCallParams := {
                            gas := gas_arg, target := address, value := value,
                            inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize
                          }
                          let executionEnv₁ := { prepareChildCallEnv .Call sharedState.executionEnv callParams calldata₁ with
                                                    code := yulContract.code }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁ }
                          let s₁ : State := .Ok sharedState₁ default
                          finishChildCallOutcome s₀ varstore outOffset outSize (callDispatcher fuel₁ .none s₁)
          | _ => .error .InvalidArguments
      | .STATICCALL =>
        match args with
          | gas_arg :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            let s₀Static : State := setStatic s₀ false
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀Static.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            if s₀Static.toSharedState.executionEnv.depth ≥ 1024 then
              buildContractCallEmptyReturnState s₀ .none ⟨0⟩
            else
              match s₀Static with
              | .OutOfFuel => .error .OutOfFuel
              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
              | .Ok sharedState varstore =>
                  match s₀Static.sharedState.accountMap.get? address with
                    | .none =>
                        buildContractCallEmptyReturnState s₀ .none ⟨1⟩
                    | .some yulContract =>
                      let callParams : YulCallParams := {
                        gas := gas_arg, target := address, value := ⟨0⟩,
                        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize
                      }
                      let executionEnv₁ := { prepareChildCallEnv .StaticCall s₀.executionEnv callParams calldata₁ with
                                                code := yulContract.code }
                      let sharedState₁ := { sharedState with
                                              executionEnv := executionEnv₁,
                                              memory := ByteArray.mk #[] }
                      let s₁ : State := .Ok sharedState₁ default
                      finishChildCallOutcome s₀ varstore outOffset outSize (callDispatcher fuel₁ .none s₁)
          | _ => .error .InvalidArguments
      | .CALLCODE =>
        match args with
          | gas_arg :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner s₀.executionEnv.codeOwner value)
            match accountMap₁Opt with
              | .none =>
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024 then
                  buildContractCallEmptyReturnState s₀ accountMap₁ ⟨0⟩
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.get? address with
                        | .none =>
                            buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩
                        | .some yulContract =>
                          let callParams : YulCallParams := {
                            gas := gas_arg, target := address, value := value,
                            inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize
                          }
                          let executionEnv₁ := { prepareChildCallEnv .CallCode sharedState.executionEnv callParams calldata₁ with
                                                    code := yulContract.code }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁ }
                          let s₁ : State := .Ok sharedState₁ default
                          finishChildCallOutcome s₀ varstore outOffset outSize (callDispatcher fuel₁ yulContract.code s₁)
          | _ => .error .InvalidArguments
      | .DELEGATECALL =>
        match args with
          | gas_arg :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            if s₀.executionEnv.depth ≥ 1024 then
              buildContractCallEmptyReturnState s₀ .none ⟨0⟩
            else
              match s₀ with
              | .OutOfFuel => .error .OutOfFuel
              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
              | .Ok sharedState varstore =>
                  match s₀.sharedState.accountMap.get? address with
                    | .none =>
                      buildContractCallEmptyReturnState s₀ .none ⟨1⟩
                    | .some yulContract =>
                      let callParams : YulCallParams := {
                        gas := gas_arg, target := address, value := s₀.executionEnv.weiValue,
                        inOffset := inOffset, inSize := inSize, outOffset := outOffset, outSize := outSize
                      }
                      let executionEnv₁ := { prepareChildCallEnv .DelegateCall sharedState.executionEnv callParams calldata₁ with
                                                code := yulContract.code }
                      let sharedState₁ := { sharedState with
                                              executionEnv := executionEnv₁,
                                              memory := ByteArray.mk #[] }
                      let s₁ : State := .Ok sharedState₁ default
                      finishChildCallOutcome s₀ varstore outOffset outSize (callDispatcher fuel₁ yulContract.code s₁)
          | _ => .error .InvalidArguments
      | _ => match step prim .none s₀ args with
              | .ok (s, lit) => .ok (s, lit.toList)
              | .error e => .error e

  def evalTail (fuel : Nat) (args : List Expr) (codeOverride : Option YulContract) : Except Yul.Exception (State × Literal) → Except Yul.Exception (State × List Literal)
    | .ok (s, arg) => 
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => cons' arg (evalArgs fuel' args codeOverride s)
    | .error e => .error e

  /--
    `evalArgs` evaluates a list of arguments.
  -/
  def evalArgs (fuel : Nat) (args : List Expr) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match args with
        | [] => .ok (s, [])
        | arg :: args =>
          evalTail fuel' args codeOverride (eval fuel' arg codeOverride s)

  /--
    `call` executes a call of a user-defined function.
    
    Intended for use when a contract is calling one of its own functions, rather than an external contract.
  -/
  def call (fuel : Nat) (args : List Literal) (yulFunctionNameOption : Option YulFunctionName) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
        match s.sharedState.accountMap.get? s.executionEnv.codeOwner with
        | .none => .error (.MissingContract (s!"{s.executionEnv.codeOwner}")) 
        | .some yulContract =>
          let code : YulContract := codeOverride.getD yulContract.code
          
          let fOpt : Option FunctionDefinition :=
            match yulFunctionNameOption with
              | .none => .some (FunctionDefinition.Def [] [] [code.dispatcher])
              | .some yulFunctionName =>
                  code.functions.lookup yulFunctionName
          match fOpt with
          | .none => .error (.MissingContractFunction (yulFunctionNameOption.getD ".none"))
          | .some f =>
            let s₁ := 👌 s.initcall f.params args
            match exec fuel' (.Block f.body) codeOverride s₁ with
              | .error e => .error e
              | .ok s₂ =>
                let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
                .ok (s₃, List.map s₂.lookup! f.rets)

  /--
    `callDispatcher` calls the dispatcher of an external contract.
    
    It expects the `calldata` and `code` to be appropriately set.
  -/
  def callDispatcher (fuel : Nat) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
          let f := FunctionDefinition.Def [] [] [s.executionEnv.code.dispatcher]
          let s₁ := 👌 s.initcall f.params []
          match exec fuel' (.Block f.body) codeOverride s₁ with
          | .error e => .error e
          | .ok s₂ =>
            let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
            .ok (s₃, List.map s₂.lookup! f.rets)

  -- Safe to call `List.head!` on return values, because the compiler throws an
  -- error when coarity is > 0 in (1) and when coarity is > 1 in all other
  -- cases.

  def evalPrimCall (fuel : ℕ) (prim : PrimOp) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) => head' (primCall fuel s prim args)
    | .error e => .error e

  def evalCall (fuel : Nat) (f : YulFunctionName) (codeOverride : Option YulContract) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => head' (call fuel' args f codeOverride s)
    | .error e => .error e

  def execPrimCall (fuel : ℕ) (prim : PrimOp) (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) => multifill' vars (primCall fuel s prim args)
    | .error e => .error e

  def execCall (fuel : Nat) (yulFunctionName : YulFunctionName) (vars : List Identifier) (codeOverride : Option YulContract) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => multifill' vars (call fuel' args yulFunctionName codeOverride s)
    | .error e => .error e

  /--
    `execSwitchCases` executes each case of a `switch` statement.
  -/
  def execSwitchCases (fuel : Nat) (codeOverride : Option YulContract) (s : State) : List (Literal × List Stmt) → Except Yul.Exception (List (Literal × (Except Yul.Exception State)))
    | [] => .ok []
    | ((val, stmts) :: cases') =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => 
        match exec fuel' (.Block stmts) codeOverride s with
          | .error (.YulHalt s₂ v) =>
            match execSwitchCases fuel' codeOverride s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .error (.YulHalt s₂ v)) :: s₃)
          | .error e =>
              match execSwitchCases fuel' codeOverride s cases' with
              | .error e => .error e
              | .ok s₃ =>
                .ok ((val, .error e) :: s₃)
          | .ok s₂ =>
            match execSwitchCases fuel' codeOverride s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .ok s₂) :: s₃)

  /--
    `eval` evaluates an expression.

    - calls evaluated here are assumed to have coarity 1
  -/
  def eval (fuel : Nat) (expr : Expr) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
        match expr with

        -- We hit these two cases (`PrimCall` and `Call`) when evaluating:
        --
        --  1. f()                 (expression statements)
        --  2. g(f())              (calls in function arguments)
        --  3. if f() {...}        (if conditions)
        --  4. for {...} f() ...   (for conditions)
        --  5. switch f() ...      (switch conditions)

        | .Call (Sum.inl prim) args => evalPrimCall fuel' prim (reverse' (evalArgs fuel' args.reverse codeOverride s))
        | .Call (Sum.inr yulFunctionName) args        =>
          evalCall fuel' yulFunctionName codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
        | .Var id             => .ok (s, s[id]!)
        | .Lit val            => .ok (s, val)

  /--
    `exec` executs a single statement.
  -/
  def exec (fuel : Nat) (stmt : Stmt) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match stmt with
        | .Block [] => .ok s
        | .Block (stmt :: stmts) =>
          let s₁ := exec fuel' stmt codeOverride s
          match s₁ with
            | .error e => .error e
            | .ok s₁ => exec fuel' (.Block stmts) codeOverride s₁

        | .Let vars exprOption =>
            match exprOption with
              | .none => .ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars)
              | .some expr =>
                match expr with
                  | .Call (Sum.inl prim) args =>
                    execPrimCall fuel' prim vars (reverse' (evalArgs fuel' args.reverse codeOverride s))
                  | .Call (Sum.inr yulFunctionName) args =>
                    execCall fuel' yulFunctionName vars codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
                  | .Var identifier => .ok (s.insert vars.head! s[identifier]!) -- It should be safe to call head! here if the Yul code is parsed correctly.
                  | .Lit literal => .ok (s.insert vars.head! literal) -- It should be safe to call head! here if the Yul code is parsed correctly.

        | .If cond body =>
          match eval fuel' cond codeOverride s with
            | .error e => .error e
            | .ok (s, cond) =>
              if cond ≠ ⟨0⟩ then exec fuel' (.Block body) codeOverride s else .ok s

        -- "Expressions that are also statements (i.e. at the block level) have
        -- to evaluate to zero values."
        --
        -- (https://docs.soliditylang.org/en/latest/yul.html#restrictions-on-the-grammar)
        --
        -- Thus, we cannot have literals or variables on the RHS.
        | .ExprStmtCall expr =>
             match expr with
               | .Call (Sum.inl prim) args => execPrimCall fuel' prim [] (reverse' (evalArgs fuel' args.reverse codeOverride s))
               | .Call (Sum.inr f) args => execCall fuel' f [] codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
               | _ => .error .InvalidExpression -- This case should never occur because we cannot have literals or variables on the RHS, as noted above.

        | .Switch cond cases' default' =>
          match eval fuel' cond codeOverride s with
            | .error e => .error e
            | .ok (s₁, cond) =>
              match execSwitchCases fuel' codeOverride s₁ cases' with
              | .error e => .error e  
              | .ok branches =>
                match exec fuel' (.Block default') codeOverride s₁ with
                | .error e => .error e
                | .ok s₂ =>
                  (List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) (.ok s₂) branches)

        -- A `Break` or `Continue` in the pre or post is a compiler error,
        -- so we assume it can't happen and don't modify the state in these
        -- cases. (https://docs.soliditylang.org/en/v0.8.23/yul.html#loops)
        | .For cond post body => (loop fuel' cond post body codeOverride s)
        | .Continue => .ok (🔁 s)
        | .Break => .ok (💔 s)
        | .Leave => .ok (🚪 s)

  /--
    `loop` executes a for-loop.
  -/
  def loop (fuel : Nat) (cond : Expr) (post body : List Stmt) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception State :=
    match fuel with
      | 0 => .error .OutOfFuel
      | 1 => .error .OutOfFuel
      | fuel' + 1 + 1 =>
        match eval fuel' cond codeOverride (👌s) with
        | .error e => .error e
        | .ok (s₁, x) =>
          if x = ⟨0⟩
            then .ok (s₁✏️⟦s⟧?)
            else
              match exec fuel' (.Block body) codeOverride s₁ with
              | .error e => .error e
              | .ok s₂ =>
                match s₂ with
                  | .OutOfFuel                      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Break _ _)      => .ok (🧟s₂✏️⟦s⟧?)
                  | .Checkpoint (.Leave _ _)      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Continue _ _)
                  | _ =>
                    match exec fuel' (.Block post) codeOverride (🧟 s₂) with
                    | .error e => .error e
                    | .ok s₃ =>
                      let s₄ := s₃✏️⟦s⟧?
                      match exec fuel' (.For cond post body) codeOverride s₄ with
                      | .error e => .error e
                      | .ok s₅ =>
                        let s₆ := s₅✏️⟦s⟧?
                        .ok s₆
end

def execTopLevel (fuel : Nat) (stmt : Stmt) (s : State) : State :=
  match exec fuel stmt .none s with
    | .error .InvalidArguments => default
    | .error .NotEncodableRLP => default
    | .error .InvalidInstruction => default
    | .error .OutOfFuel => default
    | .error .StaticModeViolation => s -- Revert, note that we do not model charging gas in the Yul semantics
    | .error (.MissingContract _) => default
    | .error (.MissingContractFunction _) => default -- We do not model fallback functions
    | .error .InvalidExpression => default
    | .error .YulEXTCODESIZENotImplemented => default
    | .error .InvalidMemoryAccess => default
    | .error (.Revert _) => s
    | .error (.YulHalt s _) => s
    | .ok s => s

notation "🍄" => exec
notation "🌸" => eval

-- ============================================================================
--  GAS-ACCOUNTING YUL PRIMITIVE CALL BRIDGE (Layer 3)
-- ============================================================================

/-- Total dynamic + memory-expansion gas cost of a Yul primitive operation under `fork`. -/
def yulOpTotalGas (fork : EVM.Fork) (s : State) (prim : Operation .Yul) (args : List Literal) : ℕ :=
  yulPrimOpDynamicGas fork s prim args + yulMemoryExpansionGas s prim args

/-- Gas-accounting wrapper around `primCall`: deducts `yulOpTotalGas fork s₀ prim args`
    via `consumeYulGas` before executing `primCall fuel s₁ prim args`. -/
def primCallWithGas (fork : EVM.Fork) (fuel : ℕ) (s₀ : State)
    (prim : Operation .Yul) (args : List Literal) :
    Except Yul.Exception (State × List Literal) := do
  let s₁ ← consumeYulGas s₀ (yulOpTotalGas fork s₀ prim args)
  primCall fuel s₁ prim args

/-- When `s₀.toMachineState.gasAvailable.toNat < yulOpTotalGas fork s₀ prim args`,
    `primCallWithGas` deterministically fails with `.error .OutOfFuel`. -/
theorem primCallWithGas_outOfFuel_of_lt (fork : EVM.Fork) (fuel : ℕ) (s₀ : State)
    (prim : Operation .Yul) (args : List Literal)
    (hLt : s₀.toMachineState.gasAvailable.toNat < yulOpTotalGas fork s₀ prim args) :
    primCallWithGas fork fuel s₀ prim args = .error .OutOfFuel := by
  unfold primCallWithGas
  have hErr : consumeYulGas s₀ (yulOpTotalGas fork s₀ prim args) = .error .OutOfFuel :=
    (consumeYulGas_outOfFuel_iff s₀ (yulOpTotalGas fork s₀ prim args)).mpr hLt
  rw [hErr]
  rfl

/-- When sufficient gas is available (`yulOpTotalGas fork s₀ prim args ≤ gasAvailable`),
    `primCallWithGas` deducts the exact operation gas and delegates to `primCall`. -/
theorem primCallWithGas_eq_primCall_of_le (fork : EVM.Fork) (fuel : ℕ) (s₀ : State)
    (prim : Operation .Yul) (args : List Literal)
    (hLe : yulOpTotalGas fork s₀ prim args ≤ s₀.toMachineState.gasAvailable.toNat) :
    primCallWithGas fork fuel s₀ prim args =
      primCall fuel
        (s₀.setMachineState
          { s₀.toMachineState with
            gasAvailable := UInt256.ofNat (s₀.toMachineState.gasAvailable.toNat - yulOpTotalGas fork s₀ prim args) })
        prim args := by
  unfold primCallWithGas consumeYulGas
  simp [hLe, Bind.bind, Except.bind]

/-- Child `.Revert data` in `finishChildCallOutcome` rolls back world state to `s₀`, copies
    `data` to the output area, makes it the returndata, and pushes `0`. -/
theorem finishChildCallOutcome_revert_rolls_back {α : Type}
    (shared₀ : EvmYul.SharedState .Yul) (varstore : VarStore) (outOffset outSize : UInt256)
    (data : ByteArray) :
    finishChildCallOutcome (.Ok shared₀ varstore) varstore outOffset outSize
      (.error (.Revert data) : Except Yul.Exception (State × α)) =
    .ok (.Ok { shared₀ with
                memory := data.copySlice 0 shared₀.memory outOffset.toNat
                  (min outSize.toNat data.size)
                H_return := ByteArray.empty
                returnData := data } varstore, [⟨0⟩]) := by
  rfl

/-- Child `.StaticModeViolation` in `finishChildCallOutcome` rolls back world state to `s₀` and pushes `0`. -/
theorem finishChildCallOutcome_staticViolation_rolls_back {α : Type}
    (shared₀ : EvmYul.SharedState .Yul) (varstore : VarStore) (outOffset outSize : UInt256) :
    finishChildCallOutcome (.Ok shared₀ varstore) varstore outOffset outSize
      (.error .StaticModeViolation : Except Yul.Exception (State × α)) =
    .ok (.Ok { shared₀ with H_return := ByteArray.empty, returnData := ByteArray.empty } varstore, [⟨0⟩]) := by
  rfl

end Yul

end EvmYul
