import EvmYul.StateOps
import EvmYul.SharedStateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.StateOps

/-!
Algebra of state lenses used to frame EVM updates.

A `StateLens` reads and writes one cell of a state. `unchangedExcept` says two
states agree on every cell of a family except possibly one named key. The laws
are the usual get/set identities, together with the concrete projections of
storage, transient storage, the account map, and substate through
`EvmYul.State`, `SharedState`, and `EVM.State`.
-/

namespace EvmYul

namespace MetaSpec

/-- A functional lens: `get` reads the cell at `k`, `set` overwrites it. -/
structure StateLens (S K V : Type) where
  get : S → K → V
  set : S → K → V → S

namespace StateLens

/-- `set` at `k` is observed by `get` at `k`. -/
def GetSetSame {S K V : Type} (L : StateLens S K V) : Prop :=
  ∀ (s : S) (k : K) (v : V), L.get (L.set s k v) k = v

/-- `set` at `k` does not disturb `get` at a different key. -/
def GetSetNe {S K V : Type} (L : StateLens S K V) : Prop :=
  ∀ (s : S) (k k' : K) (v : V), k ≠ k' → L.get (L.set s k v) k' = L.get s k'

/-- Writing twice at the same key keeps only the second value, observationally. -/
def SetSetSame {S K V : Type} (L : StateLens S K V) : Prop :=
  ∀ (s : S) (k k' : K) (v v' : V),
    L.get (L.set (L.set s k v) k v') k' = L.get (L.set s k v') k'

end StateLens

/-- `s'` agrees with `s` on every lens cell except possibly `k`. -/
def unchangedExcept {S K V : Type} (L : StateLens S K V) (s s' : S) (k : K) : Prop :=
  ∀ k', k' ≠ k → L.get s' k' = L.get s k'

theorem unchangedExcept_refl {S K V : Type} (L : StateLens S K V) (s : S) (k : K) :
    unchangedExcept L s s k :=
  fun _ _ => rfl

theorem unchangedExcept_trans {S K V : Type} (L : StateLens S K V) {s s₁ s₂ : S} {k : K}
    (h₁ : unchangedExcept L s s₁ k) (h₂ : unchangedExcept L s₁ s₂ k) :
    unchangedExcept L s s₂ k :=
  fun k' hk => (h₂ k' hk).trans (h₁ k' hk)

theorem unchangedExcept_set_self {S K V : Type} {L : StateLens S K V}
    (hne : L.GetSetNe) (s : S) (k : K) (v : V) :
    unchangedExcept L s (L.set s k v) k :=
  fun k' hk => hne s k k' v hk.symm

/-! Concrete cells. Storage and transient storage are keyed by owner and slot. -/

abbrev StorageKey (_τ : OperationType) := AccountAddress × UInt256

/-- Persistent storage of one account slot. Missing accounts and slots read as `0`. -/
def storageLens (τ : OperationType) : StateLens (State τ) (StorageKey τ) UInt256 where
  get s key :=
    match s.accountMap.get? key.1 with
    | none => ⟨0⟩
    | some acc => acc.lookupStorage key.2
  set s key v :=
    let acc := (s.accountMap.get? key.1).getD default
    s.setAccount key.1 (acc.updateStorage key.2 v)

/-- Transient storage of one account slot. Missing accounts and slots read as `0`. -/
def transientLens (τ : OperationType) : StateLens (State τ) (StorageKey τ) UInt256 where
  get s key :=
    match s.accountMap.get? key.1 with
    | none => ⟨0⟩
    | some acc => acc.lookupTransientStorage key.2
  set s key v :=
    let acc := (s.accountMap.get? key.1).getD default
    s.setAccount key.1 (acc.updateTransientStorage key.2 v)

/-- The account map itself, as a lens over addresses. -/
def accountMapLens (τ : OperationType) :
    StateLens (State τ) AccountAddress (Account τ) where
  get s addr := (s.accountMap.get? addr).getD default
  set s addr acc := s.setAccount addr acc

/-- The whole substate, as a nullary lens (one cell, no key). -/
def substateLens (τ : OperationType) : StateLens (State τ) Unit Substate where
  get s _ := s.substate
  set s _ A := { s with substate := A }

/-! Shared-state projections keep the machine component fixed. -/

def sharedStorageLens (τ : OperationType) :
    StateLens (SharedState τ) (StorageKey τ) UInt256 where
  get s := (storageLens τ).get s.toState
  set s key v := { s with toState := (storageLens τ).set s.toState key v }

def sharedTransientLens (τ : OperationType) :
    StateLens (SharedState τ) (StorageKey τ) UInt256 where
  get s := (transientLens τ).get s.toState
  set s key v := { s with toState := (transientLens τ).set s.toState key v }

def sharedAccountMapLens (τ : OperationType) :
    StateLens (SharedState τ) AccountAddress (Account τ) where
  get s := (accountMapLens τ).get s.toState
  set s addr acc := { s with toState := (accountMapLens τ).set s.toState addr acc }

def sharedSubstateLens (τ : OperationType) :
    StateLens (SharedState τ) Unit Substate where
  get s := (substateLens τ).get s.toState
  set s u A := { s with toState := (substateLens τ).set s.toState u A }

/-! EVM-state projections keep `pc`, `stack`, and `execLength` fixed. -/

def evmStorageLens : StateLens EVM.State (StorageKey .EVM) UInt256 where
  get s := (sharedStorageLens .EVM).get s.toSharedState
  set s key v := { s with toSharedState := (sharedStorageLens .EVM).set s.toSharedState key v }

def evmTransientLens : StateLens EVM.State (StorageKey .EVM) UInt256 where
  get s := (sharedTransientLens .EVM).get s.toSharedState
  set s key v := { s with toSharedState := (sharedTransientLens .EVM).set s.toSharedState key v }

def evmAccountMapLens : StateLens EVM.State AccountAddress (Account .EVM) where
  get s := (sharedAccountMapLens .EVM).get s.toSharedState
  set s addr acc := { s with toSharedState := (sharedAccountMapLens .EVM).set s.toSharedState addr acc }

def evmSubstateLens : StateLens EVM.State Unit Substate where
  get s := (sharedSubstateLens .EVM).get s.toSharedState
  set s u A := { s with toSharedState := (sharedSubstateLens .EVM).set s.toSharedState u A }

/-! Machine-state memory cell, keyed by byte address. -/

def memoryLens : StateLens MachineState UInt256 UInt8 where
  get μ addr := μ.memory.data.getD addr.toNat 0
  set μ addr b :=
    { μ with memory := μ.memory.set! addr.toNat b }

instance : Std.TransCmp (compare : AccountAddress → AccountAddress → Ordering) where
  eq_swap {a b} :=
    Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)) (a := a.val) (b := b.val)
  isLE_trans {a b c} h₁ h₂ :=
    Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering)) (a := a.val) (b := b.val) (c := c.val) h₁ h₂

instance : Std.LawfulEqCmp (compare : AccountAddress → AccountAddress → Ordering) where
  eq_of_compare {a b} h :=
    Fin.ext (Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Nat → Nat → Ordering)) (a := a.val) (b := b.val) h)
  compare_self {a} :=
    Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering)) (a := a.val)

private theorem lookupStorage_updateStorage_same (τ : OperationType) (acc : Account τ) (k v : UInt256) :
    (acc.updateStorage k v).lookupStorage k = v := by
  unfold Account.updateStorage Account.lookupStorage
  by_cases hv : v == (default : UInt256)
  · have hv0 : v = default := eq_of_beq hv
    simp only [hv, ↓reduceIte, Std.TreeMap.getD_erase_self]
    exact hv0.symm
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getD_insert_self]

private theorem lookupStorage_updateStorage_ne (τ : OperationType) (acc : Account τ) {k k' v : UInt256}
    (h : k ≠ k') : (acc.updateStorage k v).lookupStorage k' = acc.lookupStorage k' := by
  unfold Account.updateStorage Account.lookupStorage
  by_cases hv : v == (default : UInt256)
  · simp only [hv, ↓reduceIte, Std.TreeMap.getD_erase]
    simp [h]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getD_insert]
    simp [h]

private theorem lookupTransient_updateTransient_same (τ : OperationType) (acc : Account τ)
    (k v : UInt256) :
    (acc.updateTransientStorage k v).lookupTransientStorage k = v := by
  unfold Account.updateTransientStorage Account.lookupTransientStorage
  by_cases hv : v == (default : UInt256)
  · have hv0 : v = default := eq_of_beq hv
    simp only [hv, ↓reduceIte, Std.TreeMap.getD_erase_self]
    exact hv0.symm
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getD_insert_self]

private theorem lookupTransient_updateTransient_ne (τ : OperationType) (acc : Account τ)
    {k k' v : UInt256} (h : k ≠ k') :
    (acc.updateTransientStorage k v).lookupTransientStorage k' =
      acc.lookupTransientStorage k' := by
  unfold Account.updateTransientStorage Account.lookupTransientStorage
  by_cases hv : v == (default : UInt256)
  · simp only [hv, ↓reduceIte, Std.TreeMap.getD_erase]
    simp [h]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getD_insert]
    simp [h]

private theorem setAccount_get_same (τ : OperationType) (s : State τ) (addr : AccountAddress)
    (acc : Account τ) :
    ((s.setAccount addr acc).accountMap.get? addr) = some acc := by
  simp [State.setAccount]

private theorem setAccount_get_ne (τ : OperationType) (s : State τ) {addr addr' : AccountAddress}
    (acc : Account τ) (h : addr ≠ addr') :
    ((s.setAccount addr acc).accountMap.get? addr') = s.accountMap.get? addr' := by
  simp [State.setAccount, Std.TreeMap.getElem?_insert]
  intro heq
  exact absurd heq h

theorem storageLens_get_set_same (τ : OperationType) :
    (storageLens τ).GetSetSame := by
  intro s key v
  unfold StateLens.get StateLens.set storageLens
  simp only
  have hg := setAccount_get_same τ s key.1
    (((s.accountMap.get? key.1).getD default).updateStorage key.2 v)
  simp only [hg]
  exact lookupStorage_updateStorage_same τ _ key.2 v

theorem storageLens_get_set_ne (τ : OperationType) :
    (storageLens τ).GetSetNe := by
  intro s key key' v hne
  rcases key with ⟨owner, slot⟩
  rcases key' with ⟨owner', slot'⟩
  unfold StateLens.get StateLens.set storageLens
  simp only
  by_cases howner : owner = owner'
  · subst howner
    have hslot : slot ≠ slot' := by
      intro hs
      exact hne (congrArg (Prod.mk owner) hs)
    have hg := setAccount_get_same τ s owner
      (((s.accountMap.get? owner).getD default).updateStorage slot v)
    simp only [hg]
    have hlookup :=
      lookupStorage_updateStorage_ne τ ((s.accountMap.get? owner).getD default)
        (k := slot) (k' := slot') (v := v) hslot
    simp only [hlookup]
    cases s.accountMap.get? owner <;> rfl
  · have hg := setAccount_get_ne τ s
      (((s.accountMap.get? owner).getD default).updateStorage slot v) howner
    rw [hg]

theorem storageLens_set_set_same (τ : OperationType) :
    (storageLens τ).SetSetSame := by
  intro s key key' v v'
  by_cases h : key = key'
  · subst h
    rw [storageLens_get_set_same, storageLens_get_set_same]
  · have h₁ := storageLens_get_set_ne τ ((storageLens τ).set s key v) key key' v' h
    have h₂ := storageLens_get_set_ne τ s key key' v' h
    have h₃ := storageLens_get_set_ne τ s key key' v h
    exact h₁.trans (h₃.trans h₂.symm)

theorem transientLens_get_set_same (τ : OperationType) :
    (transientLens τ).GetSetSame := by
  intro s key v
  unfold StateLens.get StateLens.set transientLens
  simp only
  have hg := setAccount_get_same τ s key.1
    (((s.accountMap.get? key.1).getD default).updateTransientStorage key.2 v)
  simp only [hg]
  exact lookupTransient_updateTransient_same τ _ key.2 v

theorem transientLens_get_set_ne (τ : OperationType) :
    (transientLens τ).GetSetNe := by
  intro s key key' v hne
  rcases key with ⟨owner, slot⟩
  rcases key' with ⟨owner', slot'⟩
  unfold StateLens.get StateLens.set transientLens
  simp only
  by_cases howner : owner = owner'
  · subst howner
    have hslot : slot ≠ slot' := by
      intro hs
      exact hne (congrArg (Prod.mk owner) hs)
    have hg := setAccount_get_same τ s owner
      (((s.accountMap.get? owner).getD default).updateTransientStorage slot v)
    simp only [hg]
    have hlookup :=
      lookupTransient_updateTransient_ne τ ((s.accountMap.get? owner).getD default)
        (k := slot) (k' := slot') (v := v) hslot
    simp only [hlookup]
    cases s.accountMap.get? owner <;> rfl
  · have hg := setAccount_get_ne τ s
      (((s.accountMap.get? owner).getD default).updateTransientStorage slot v) howner
    rw [hg]

theorem transientLens_set_set_same (τ : OperationType) :
    (transientLens τ).SetSetSame := by
  intro s key key' v v'
  by_cases h : key = key'
  · subst h
    rw [transientLens_get_set_same, transientLens_get_set_same]
  · have h₁ := transientLens_get_set_ne τ ((transientLens τ).set s key v) key key' v' h
    have h₂ := transientLens_get_set_ne τ s key key' v' h
    have h₃ := transientLens_get_set_ne τ s key key' v h
    exact h₁.trans (h₃.trans h₂.symm)

theorem accountMapLens_get_set_same (τ : OperationType) :
    (accountMapLens τ).GetSetSame := by
  intro s addr acc
  unfold StateLens.get StateLens.set accountMapLens
  simp only [setAccount_get_same, Option.getD_some]

theorem accountMapLens_get_set_ne (τ : OperationType) :
    (accountMapLens τ).GetSetNe := by
  intro s addr addr' acc hne
  unfold StateLens.get StateLens.set accountMapLens
  simp only [setAccount_get_ne τ _ _ hne]

theorem accountMapLens_set_set_same (τ : OperationType) :
    (accountMapLens τ).SetSetSame := by
  intro s addr addr' acc acc'
  by_cases h : addr = addr'
  · subst h
    rw [accountMapLens_get_set_same, accountMapLens_get_set_same]
  · have h₁ := accountMapLens_get_set_ne τ ((accountMapLens τ).set s addr acc) addr addr' acc' h
    have h₂ := accountMapLens_get_set_ne τ s addr addr' acc' h
    have h₃ := accountMapLens_get_set_ne τ s addr addr' acc h
    exact h₁.trans (h₃.trans h₂.symm)

theorem substateLens_get_set_same (τ : OperationType) :
    (substateLens τ).GetSetSame := by
  intro s u A
  cases u
  rfl

theorem substateLens_get_set_ne (τ : OperationType) :
    (substateLens τ).GetSetNe := by
  intro s u u' A hne
  cases u
  cases u'
  exact absurd rfl hne

theorem substateLens_set_set_same (τ : OperationType) :
    (substateLens τ).SetSetSame := by
  intro s u u' A A'
  cases u
  cases u'
  rfl

theorem storage_unchangedExcept_set (τ : OperationType) (s : State τ) (key : StorageKey τ)
    (v : UInt256) :
    unchangedExcept (storageLens τ) s ((storageLens τ).set s key v) key :=
  unchangedExcept_set_self (storageLens_get_set_ne τ) s key v

theorem transient_unchangedExcept_set (τ : OperationType) (s : State τ) (key : StorageKey τ)
    (v : UInt256) :
    unchangedExcept (transientLens τ) s ((transientLens τ).set s key v) key :=
  unchangedExcept_set_self (transientLens_get_set_ne τ) s key v

theorem accountMap_unchangedExcept_set (τ : OperationType) (s : State τ) (addr : AccountAddress)
    (acc : Account τ) :
    unchangedExcept (accountMapLens τ) s ((accountMapLens τ).set s addr acc) addr :=
  unchangedExcept_set_self (accountMapLens_get_set_ne τ) s addr acc

/-- Storage writes do not touch the substate. -/
theorem storage_preserves_substate (τ : OperationType) (s : State τ) (key : StorageKey τ)
    (v : UInt256) :
    ((storageLens τ).set s key v).substate = s.substate := by
  unfold storageLens StateLens.set State.setAccount
  rfl

/-- Transient writes do not touch the substate. -/
theorem transient_preserves_substate (τ : OperationType) (s : State τ) (key : StorageKey τ)
    (v : UInt256) :
    ((transientLens τ).set s key v).substate = s.substate := by
  unfold transientLens StateLens.set State.setAccount
  rfl

/-- Account-map writes do not touch the substate. -/
theorem accountMap_preserves_substate (τ : OperationType) (s : State τ) (addr : AccountAddress)
    (acc : Account τ) :
    ((accountMapLens τ).set s addr acc).substate = s.substate := by
  unfold accountMapLens StateLens.set State.setAccount
  rfl

/-- Substate writes do not touch the account map. -/
theorem substate_preserves_accountMap (τ : OperationType) (s : State τ) (A : Substate) :
    ((substateLens τ).set s () A).accountMap = s.accountMap := by
  rfl

/-- Substate writes do not touch storage cells. -/
theorem substate_preserves_storage (τ : OperationType) (s : State τ) (A : Substate)
    (key : StorageKey τ) :
    (storageLens τ).get ((substateLens τ).set s () A) key = (storageLens τ).get s key := by
  unfold storageLens substateLens StateLens.get StateLens.set
  rfl

/-- Substate writes do not touch transient cells. -/
theorem substate_preserves_transient (τ : OperationType) (s : State τ) (A : Substate)
    (key : StorageKey τ) :
    (transientLens τ).get ((substateLens τ).set s () A) key = (transientLens τ).get s key := by
  unfold transientLens substateLens StateLens.get StateLens.set
  rfl

/-! SharedState projections preserve the machine component. -/

theorem sharedStorage_preserves_machine (τ : OperationType) (s : SharedState τ) (key : StorageKey τ)
    (v : UInt256) :
    ((sharedStorageLens τ).set s key v).toMachineState = s.toMachineState := by
  rfl

theorem sharedTransient_preserves_machine (τ : OperationType) (s : SharedState τ)
    (key : StorageKey τ) (v : UInt256) :
    ((sharedTransientLens τ).set s key v).toMachineState = s.toMachineState := by
  rfl

theorem sharedAccountMap_preserves_machine (τ : OperationType) (s : SharedState τ)
    (addr : AccountAddress) (acc : Account τ) :
    ((sharedAccountMapLens τ).set s addr acc).toMachineState = s.toMachineState := by
  rfl

theorem sharedSubstate_preserves_machine (τ : OperationType) (s : SharedState τ) (A : Substate) :
    ((sharedSubstateLens τ).set s () A).toMachineState = s.toMachineState := by
  rfl

theorem sharedStorage_get_set_same (τ : OperationType) :
    (sharedStorageLens τ).GetSetSame :=
  fun s key v => storageLens_get_set_same τ s.toState key v

theorem sharedStorage_get_set_ne (τ : OperationType) :
    (sharedStorageLens τ).GetSetNe :=
  fun s key key' v hne => storageLens_get_set_ne τ s.toState key key' v hne

theorem sharedStorage_set_set_same (τ : OperationType) :
    (sharedStorageLens τ).SetSetSame :=
  fun s key key' v v' => storageLens_set_set_same τ s.toState key key' v v'

theorem sharedTransient_get_set_same (τ : OperationType) :
    (sharedTransientLens τ).GetSetSame :=
  fun s key v => transientLens_get_set_same τ s.toState key v

theorem sharedTransient_get_set_ne (τ : OperationType) :
    (sharedTransientLens τ).GetSetNe :=
  fun s key key' v hne => transientLens_get_set_ne τ s.toState key key' v hne

theorem sharedTransient_set_set_same (τ : OperationType) :
    (sharedTransientLens τ).SetSetSame :=
  fun s key key' v v' => transientLens_set_set_same τ s.toState key key' v v'

theorem sharedAccountMap_get_set_same (τ : OperationType) :
    (sharedAccountMapLens τ).GetSetSame :=
  fun s addr acc => accountMapLens_get_set_same τ s.toState addr acc

theorem sharedAccountMap_get_set_ne (τ : OperationType) :
    (sharedAccountMapLens τ).GetSetNe :=
  fun s addr addr' acc hne => accountMapLens_get_set_ne τ s.toState addr addr' acc hne

theorem sharedAccountMap_set_set_same (τ : OperationType) :
    (sharedAccountMapLens τ).SetSetSame :=
  fun s addr addr' acc acc' => accountMapLens_set_set_same τ s.toState addr addr' acc acc'

theorem sharedSubstate_get_set_same (τ : OperationType) :
    (sharedSubstateLens τ).GetSetSame := by
  intro s u A
  cases u
  rfl

theorem sharedSubstate_preserves_storage (τ : OperationType) (s : SharedState τ) (A : Substate)
    (key : StorageKey τ) :
    (sharedStorageLens τ).get ((sharedSubstateLens τ).set s () A) key =
      (sharedStorageLens τ).get s key :=
  substate_preserves_storage τ s.toState A key

theorem sharedSubstate_preserves_accountMap (τ : OperationType) (s : SharedState τ) (A : Substate)
    (addr : AccountAddress) :
    (sharedAccountMapLens τ).get ((sharedSubstateLens τ).set s () A) addr =
      (sharedAccountMapLens τ).get s addr :=
  rfl

/-! EVM.State projections preserve pc, stack, and execLength. -/

theorem evmStorage_preserves_pc (s : EVM.State) (key : StorageKey .EVM) (v : UInt256) :
    (evmStorageLens.set s key v).pc = s.pc := by
  rfl

theorem evmStorage_preserves_stack (s : EVM.State) (key : StorageKey .EVM) (v : UInt256) :
    (evmStorageLens.set s key v).stack = s.stack := by
  rfl

theorem evmStorage_preserves_execLength (s : EVM.State) (key : StorageKey .EVM) (v : UInt256) :
    (evmStorageLens.set s key v).execLength = s.execLength := by
  rfl

theorem evmTransient_preserves_pc (s : EVM.State) (key : StorageKey .EVM) (v : UInt256) :
    (evmTransientLens.set s key v).pc = s.pc := by
  rfl

theorem evmAccountMap_preserves_stack (s : EVM.State) (addr : AccountAddress) (acc : Account .EVM) :
    (evmAccountMapLens.set s addr acc).stack = s.stack := by
  rfl

theorem evmSubstate_preserves_pc (s : EVM.State) (A : Substate) :
    (evmSubstateLens.set s () A).pc = s.pc := by
  rfl

theorem evmSubstate_preserves_machine (s : EVM.State) (A : Substate) :
    (evmSubstateLens.set s () A).toMachineState = s.toMachineState := by
  rfl

theorem evmStorage_get_set_same :
    evmStorageLens.GetSetSame :=
  fun s key v => sharedStorage_get_set_same .EVM s.toSharedState key v

theorem evmStorage_get_set_ne :
    evmStorageLens.GetSetNe :=
  fun s key key' v hne => sharedStorage_get_set_ne .EVM s.toSharedState key key' v hne

theorem evmStorage_set_set_same :
    evmStorageLens.SetSetSame :=
  fun s key key' v v' => sharedStorage_set_set_same .EVM s.toSharedState key key' v v'

theorem evmTransient_get_set_same :
    evmTransientLens.GetSetSame :=
  fun s key v => sharedTransient_get_set_same .EVM s.toSharedState key v

theorem evmTransient_get_set_ne :
    evmTransientLens.GetSetNe :=
  fun s key key' v hne => sharedTransient_get_set_ne .EVM s.toSharedState key key' v hne

theorem evmAccountMap_get_set_same :
    evmAccountMapLens.GetSetSame :=
  fun s addr acc => sharedAccountMap_get_set_same .EVM s.toSharedState addr acc

theorem evmAccountMap_get_set_ne :
    evmAccountMapLens.GetSetNe :=
  fun s addr addr' acc hne => sharedAccountMap_get_set_ne .EVM s.toSharedState addr addr' acc hne

theorem evmSubstate_get_set_same :
    evmSubstateLens.GetSetSame := by
  intro s u A
  cases u
  rfl

theorem evmSubstate_preserves_storage (s : EVM.State) (A : Substate) (key : StorageKey .EVM) :
    evmStorageLens.get (evmSubstateLens.set s () A) key = evmStorageLens.get s key :=
  sharedSubstate_preserves_storage .EVM s.toSharedState A key

/-- `sstore` writes the storage lens cell of the executing account when that account exists. -/
theorem sstore_eq_storageLens (τ : OperationType) (s : State τ) (spos sval : UInt256)
    (acc : Account τ) (hacc : s.lookupAccount s.executionEnv.codeOwner = some acc) :
    (storageLens τ).get (State.sstore s spos sval) (s.executionEnv.codeOwner, spos) = sval := by
  unfold State.sstore storageLens StateLens.get
  dsimp only
  cases (Std.TreeMap.get! s.accountMap s.executionEnv.codeOwner)
  dsimp only
  rw [hacc]
  dsimp only [Option.option, State.addAccessedStorageKey]
  rw [setAccount_get_same]
  exact lookupStorage_updateStorage_same τ acc spos sval

end MetaSpec

end EvmYul
