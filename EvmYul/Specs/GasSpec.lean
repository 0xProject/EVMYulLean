import EvmYul.EVM.Gas

namespace EvmYul.EVM

theorem L_le_self (n : ℕ) : L n ≤ n := Nat.sub_le _ _

/-- The requested positive-input strict bound is false already at one. -/
theorem L_one_eq_one : L 1 = 1 := by decide

/-- Item 2 of the requested specification is refuted by the positive input one. -/
theorem not_L_lt_self_of_pos : ¬ (∀ n : ℕ, 0 < n → L n < n) := by
  intro h
  have h1 := h 1 (by decide)
  simp [L] at h1

/-- Strictness starts exactly when the deducted sixty-fourth is nonzero. -/
theorem L_lt_self_of_ge_64 {n : ℕ} (h : 64 ≤ n) : L n < n := by
  unfold L
  omega

theorem L_monotone {m n : ℕ} (h : m ≤ n) : L m ≤ L n := by
  unfold L
  omega

theorem Cm_zero : Cₘ ⟨0⟩ = 0 := by rfl

theorem csloadPure_warm_le_cold (fork : Fork) :
    CsloadPure fork true ≤ CsloadPure fork false := by
  unfold CsloadPure
  cases fork.hasEIP2929 <;> decide

theorem csstorePure_warm_le_cold (fork : Fork) (v₀ v v' : UInt256) :
    CsstorePure fork v₀ v v' true ≤ CsstorePure fork v₀ v v' false := by
  unfold CsstorePure
  cases fork.hasEIP2929 <;> simp

theorem csstorePure_noop_eq_warm (fork : Fork) (v₀ v : UInt256) :
    CsstorePure fork v₀ v v true = GasConstants.Gwarmaccess := by
  simp [CsstorePure]

theorem ckeccak256Pure_monotone {s₁ s₂ : UInt256}
    (h : s₁.toNat ≤ s₂.toNat) : Ckeccak256Pure s₁ ≤ Ckeccak256Pure s₂ := by
  unfold Ckeccak256Pure
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.add_le_add_right h 31))) _

theorem clogPure_topic_monotone {t₁ t₂ : ℕ} (sz : UInt256) (h : t₁ ≤ t₂) :
    ClogPure t₁ sz ≤ ClogPure t₂ sz := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem intrinsicGas_prague_ge_cancun (T : Transaction) :
    intrinsicGas T .Cancun ≤ intrinsicGas T .Prague := by
  simp only [intrinsicGas, Fork.hasEIP7623, Bool.false_eq_true, ↓reduceIte]
  exact le_max_left _ _

end EvmYul.EVM
