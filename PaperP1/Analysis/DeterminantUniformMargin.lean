module

public import PaperP1.Analysis.DeterminantStrictMargin

/-! # Degree choices and one common threshold precede every local point family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantUniformMargin

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantChartBound

def constantSum (Amax B : ℕ) : ℝ := ∑ A ∈ range (Amax + 1), constant A B

theorem constant_le_sum (Amax A B : ℕ) (hA : A ≤ Amax) : constant A B ≤ constantSum Amax B := by
  exact single_le_sum (fun i _ ↦ (DeterminantExplicitDecay.constant_positive i B).le)
    (mem_range.mpr (Nat.lt_succ_of_le hA))

theorem constantSum_positive (Amax B : ℕ) : 0 < constantSum Amax B :=
  (DeterminantExplicitDecay.constant_positive 0 B).trans_le (constant_le_sum Amax 0 B (Nat.zero_le _))

theorem constants_absorbed (Amax B : ℕ) (T : ℝ)
    (hT : Real.log (constantSum Amax B) + 1 ≤ T) :
    ∀ A ≤ Amax, constant A B * Real.exp (-T) < 1 := by
  intro A hA
  calc
    _ ≤ constantSum Amax B * Real.exp (-T) :=
      mul_le_mul_of_nonneg_right (constant_le_sum Amax A B hA) (Real.exp_pos _).le
    _ = Real.exp (Real.log (constantSum Amax B) - T) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (constantSum_positive Amax B)]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hT])

theorem uniform_degrees_and_threshold (δ C W η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B Amax : ℕ, ∃ T₀ : ℝ, 0 < B ∧ 0 < T₀ ∧ ∀ T ≥ T₀, ∀ a b σ τ : ℝ,
      δ ≤ a → a ≤ C → δ ≤ b → b ≤ C → 0 < σ → 0 < τ → σ + τ ≤ W →
      (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ →
      ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧
        ((A : ℝ) * a + B * b) / 2 + (σ + τ) + 1 ≤
          (2 / 3 : ℝ) * Real.sqrt (2 * ((A + 1) * (B + 1) : ℕ) * σ * τ) ∧
        constant A B * Real.exp (-T) < 1 := by
  obtain ⟨B, Amax, hB, hchoice⟩ := DeterminantDegreeChoice.exists_uniform_degrees δ C W η hδ hη
  let T₀ := max 1 (Real.log (constantSum Amax B) + 1)
  refine ⟨B, Amax, T₀, hB, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _), ?_⟩
  intro T hT a b σ τ hδa haC hδb hbC hσ hτ hweights hproduct
  obtain ⟨A, hA₀, hA, hmargin⟩ := hchoice a b σ τ hδa haC hδb hbC hσ hτ hweights hproduct
  exact ⟨A, hA₀, hA, hmargin, constants_absorbed Amax B T ((le_max_right _ _).trans hT) A hA⟩

theorem uniform_local_smallness (δ C W η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B Amax : ℕ, ∃ T₀ : ℝ, 0 < B ∧ 0 < T₀ ∧ ∀ T ≥ T₀, ∀ a b σ τ : ℝ,
      δ ≤ a → a ≤ C → δ ≤ b → b ≤ C → 0 < σ → 0 < τ → σ + τ ≤ W →
      (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ →
      ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧
      ∀ s t α β e u : Exponent A B → ℝ, ∀ E U s₀ t₀ : ℝ,
        0 < E → 0 < U → 0 < s₀ → 0 < t₀ →
        Real.log (E ^ 2 * s₀) = a * T → Real.log (U ^ 2 * t₀) = b * T →
        (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ u i) → (∀ i, e i ≤ E) → (∀ i, u i ≤ U) →
        (∀ i, s i = s₀ * (1 + α i)) →
        (∀ i, t i = t₀ * (1 + 2 * α i + α i ^ 2 + β i)) →
        (∀ i, |α i| ≤ Real.exp (-(σ * T))) →
        (∀ i, |β i| ≤ Real.exp (-(τ * T))) →
        |(Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val)).det| *
          (∏ i, e i ^ A * u i ^ B) < 1 := by
  obtain ⟨B, Amax, T₀, hB, hT₀, hchoice⟩ := uniform_degrees_and_threshold δ C W η hδ hη
  refine ⟨B, Amax, T₀, hB, hT₀, ?_⟩
  intro T hT a b σ τ hδa haC hδb hbC hσ hτ hweights hproduct
  obtain ⟨A, hA₀, hA, hmargin, hconstant⟩ := hchoice T hT a b σ τ hδa haC hδb hbC hσ hτ hweights hproduct
  refine ⟨A, hA₀, hA, ?_⟩
  intro s t α β e u E U s₀ t₀ hE hU hs₀ ht₀ ha hb he₀ hu₀ he hu hs ht hα hβ
  exact DeterminantStrictMargin.cleared_determinant_small A B s t α β e u E U s₀ t₀ a b σ τ T
    hE hU hs₀ ht₀ hσ hτ (hT₀.trans_le hT) ha hb he₀ hu₀ he hu hs ht hα hβ hmargin hconstant

end PaperP1.DeterminantUniformMargin
