module

public import PaperP1.Algebra.QuadraticCumulantBound

/-! # Every fixed cumulant of order at least three is bounded by the common quadratic moment error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCumulantControl

open Finset PowerSeries PaperP1.FormalFactorialCumulants PaperP1.QuadraticCumulantBound

theorem finite_bound (n : ℕ) (hn : 3 ≤ n) (M : ℝ) (hM : 1 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : ℝ⟦X⟧, ∀ μ a τ : ℝ, Data f μ a M τ n → |cumulant f n| ≤ B * τ := by
  classical
  have hmain : ∀ r : ℕ, 3 ≤ r → ∃ B : ℝ, 0 ≤ B ∧
      ∀ f : ℝ⟦X⟧, ∀ μ a τ : ℝ, Data f μ a M τ r → |cumulant f r| ≤ B * τ := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      let J := Icc 3 (r - 1)
      have hper (i : J) : ∃ B : ℝ, 0 ≤ B ∧
          ∀ f : ℝ⟦X⟧, ∀ μ a τ : ℝ, Data f μ a M τ i.val → |cumulant f i.val| ≤ B * τ := by
        have hidata := mem_Icc.mp i.property
        exact ih i.val (by omega) hidata.1
      choose B hB hb using hper
      let K := fun i : ℕ ↦ if hi : i + 1 ∈ J then B ⟨i + 1, hi⟩ else 0
      have hK (i : ℕ) : 0 ≤ K i := by
        dsimp only [K]
        split_ifs with hi
        · exact hB _
        · exact le_rfl
      refine ⟨budget M K r, budget_nonneg M ((by norm_num : (0 : ℝ) ≤ 1).trans hM) K hK r, ?_⟩
      intro f μ a τ d
      apply step_bound f μ a M τ r hr hM d K hK
      intro i hi
      have hidata := mem_Icc.mp hi
      have hiJ : i + 1 ∈ J := mem_Icc.mpr ⟨by omega, by omega⟩
      have hsmall : (⟨i + 1, hiJ⟩ : J).val ≤ r := by
        change i + 1 ≤ r
        omega
      have h := hb ⟨i + 1, hiJ⟩ f μ a τ (d.mono hsmall)
      simpa only [K, dite_eq_left hiJ] using h
  exact hmain n hn

end PaperP1.FiniteCumulantControl
