module

public import PaperP1.Arithmetic.ActualRelativeDeterminant

/-! # Explicit original-equation local chart data, with no determinant hypothesis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantLocalChart

open Finset PaperP1.DeterminantIntegerRows PaperP1.TwoKernelDeterminantBoxes
  PaperP1.DeterminantRelativeChart PaperP1.ActualRelativeDeterminant

structure Data (T δ C W η : ℝ) where
  E : ℝ
  U : ℝ
  c₁ : ℝ
  c₂ : ℝ
  h : ℝ
  s₀ : ℝ
  a : ℝ
  b : ℝ
  σ : ℝ
  τ : ℝ
  E_pos : 0 < E
  U_pos : 0 < U
  c₁_pos : 0 < c₁
  c₂_pos : 0 < c₂
  s₀_pos : 0 < s₀
  first_log : Real.log (E ^ 2 * s₀) = a * T
  second_log : Real.log (U ^ 2 * center c₁ c₂ s₀) = b * T
  first_lower : δ ≤ a
  first_upper : a ≤ C
  second_lower : δ ≤ b
  second_upper : b ≤ C
  horizontal_pos : 0 < σ
  vertical_pos : 0 < τ
  weight_sum : σ + τ ≤ W
  weight_product : (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ

theorem minors_small {T δ C W η : ℝ} (D : Data T δ C W η) (hT : 0 < T) (A B : ℕ)
    (hmargin : ((A : ℝ) * D.a + B * D.b) / 2 + (D.σ + D.τ) + 1 ≤
      (2 / 3 : ℝ) * Real.sqrt (2 * ((A + 1) * (B + 1) : ℕ) * D.σ * D.τ))
    (hconstant : DeterminantChartBound.constant A B * Real.exp (-T) < 1)
    (S : Finset Quad) (he : ∀ p ∈ S, 0 < p.1.2) (hu : ∀ p ∈ S, 0 < p.2.1)
    (hebox : ∀ p ∈ S, (p.1.2 : ℝ) ≤ D.E) (hubox : ∀ p ∈ S, (p.2.1 : ℝ) ≤ D.U)
    (heq : ∀ p ∈ S, D.c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = D.c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + D.h)
    (hα : ∀ p ∈ S, |relativeAlpha D.s₀ p| ≤ Real.exp (-(D.σ * T)))
    (hβ : ∀ p ∈ S, |relativeError D.c₁ D.c₂ D.h D.s₀ p| ≤ Real.exp (-(D.τ * T))) :
    ∀ P : Exponent A B → S, |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
      (∏ i, denominator A B (P i).val) < 1 := by
  intro P
  apply small_of_real_small
  apply DeterminantStrictMargin.cleared_determinant_small A B
    (fun i ↦ firstRatio (P i).val) (fun i ↦ secondRatio (P i).val)
    (fun i ↦ relativeAlpha D.s₀ (P i).val) (fun i ↦ relativeError D.c₁ D.c₂ D.h D.s₀ (P i).val)
    (fun i ↦ ((P i).val.1.2 : ℝ)) (fun i ↦ ((P i).val.2.1 : ℝ))
    D.E D.U D.s₀ (center D.c₁ D.c₂ D.s₀) D.a D.b D.σ D.τ T
    D.E_pos D.U_pos D.s₀_pos (center_positive D.c₁_pos D.c₂_pos D.s₀_pos)
    D.horizontal_pos D.vertical_pos hT D.first_log D.second_log
    (fun i ↦ Nat.cast_nonneg _) (fun i ↦ Nat.cast_nonneg _)
    (fun i ↦ hebox _ (P i).property) (fun i ↦ hubox _ (P i).property)
    (fun i ↦ first_normalization _ D.s₀_pos (he _ (P i).property))
    (fun i ↦ second_normalization _ D.c₁_pos D.c₂_pos D.s₀_pos
      (he _ (P i).property) (hu _ (P i).property) (heq _ (P i).property))
    (fun i ↦ hα _ (P i).property) (fun i ↦ hβ _ (P i).property) hmargin hconstant

end PaperP1.DeterminantLocalChart
