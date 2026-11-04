module

public import PaperP1.Analysis.DeterminantDenominatorBudget

/-! # A strict degree margin makes every cleared local determinant smaller than one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantStrictMargin

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantChartBound
  PaperP1.DeterminantExplicitDecay PaperP1.DeterminantDenominatorBudget

theorem lowerCost_scaling (H : ℕ) (σ τ T : ℝ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hT : 0 ≤ T) :
    lowerCost H (σ * T) (τ * T) = (H : ℝ) * T *
      ((2 / 3 : ℝ) * Real.sqrt (2 * H * σ * τ) - (σ + τ)) := by
  have he : 2 * (σ * T) * (τ * T) * H = (2 * (H : ℝ) * σ * τ) * T ^ 2 := by ring
  unfold lowerCost
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hT]
  ring

theorem degree_margin_cost (A B : ℕ) (a b σ τ T : ℝ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hT : 0 ≤ T)
    (hmargin : ((A : ℝ) * a + B * b) / 2 + (σ + τ) + 1 ≤
      (2 / 3 : ℝ) * Real.sqrt (2 * ((A + 1) * (B + 1) : ℕ) * σ * τ)) :
    (((A + 1) * (B + 1) : ℕ) : ℝ) * T * (((A : ℝ) * a + B * b) / 2) -
      lowerCost ((A + 1) * (B + 1)) (σ * T) (τ * T) ≤
        -((((A + 1) * (B + 1) : ℕ) : ℝ) * T) := by
  rw [lowerCost_scaling _ σ τ T hσ hτ hT]
  have hm := mul_le_mul_of_nonneg_left hmargin
    (mul_nonneg (Nat.cast_nonneg ((A + 1) * (B + 1))) hT)
  nlinarith only [hm]

theorem cleared_determinant_small (A B : ℕ)
    (s t α β e u : Exponent A B → ℝ) (E U s₀ t₀ a b σ τ T : ℝ)
    (hE : 0 < E) (hU : 0 < U) (hs₀ : 0 < s₀) (ht₀ : 0 < t₀)
    (hσ : 0 < σ) (hτ : 0 < τ) (hT : 0 < T)
    (ha : Real.log (E ^ 2 * s₀) = a * T) (hb : Real.log (U ^ 2 * t₀) = b * T)
    (he₀ : ∀ i, 0 ≤ e i) (hu₀ : ∀ i, 0 ≤ u i)
    (he : ∀ i, e i ≤ E) (hu : ∀ i, u i ≤ U)
    (hs : ∀ i, s i = s₀ * (1 + α i))
    (ht : ∀ i, t i = t₀ * (1 + 2 * α i + α i ^ 2 + β i))
    (hα : ∀ i, |α i| ≤ Real.exp (-(σ * T)))
    (hβ : ∀ i, |β i| ≤ Real.exp (-(τ * T)))
    (hmargin : ((A : ℝ) * a + B * b) / 2 + (σ + τ) + 1 ≤
      (2 / 3 : ℝ) * Real.sqrt (2 * ((A + 1) * (B + 1) : ℕ) * σ * τ))
    (hconstant : constant A B * Real.exp (-T) < 1) :
    |(Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val)).det| *
      (∏ i, e i ^ A * u i ^ B) < 1 := by
  let H := (A + 1) * (B + 1)
  let R := ∏ i, e i ^ A * u i ^ B
  let S := ∏ j : Exponent A B, s₀ ^ j.1.val * t₀ ^ j.2.val
  have hR : 0 ≤ R := prod_nonneg (fun i _ ↦ mul_nonneg (pow_nonneg (he₀ i) _) (pow_nonneg (hu₀ i) _))
  have hS : 0 < S := column_product_positive A B hs₀ ht₀
  have hHN : 0 < H := by dsimp [H]; positivity
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hHN.ne'
  have hd := original_explicit_bound A B s t α β s₀ t₀ (σ * T) (τ * T)
    (mul_pos hσ hT) (mul_pos hτ hT) hs ht hα hβ
  rw [abs_of_pos hS] at hd
  have hp := total_product_bound A B e u hE hU hs₀ ht₀ he₀ hu₀ he hu
  rw [ha, hb] at hp
  have hbudget : R * S ≤ Real.exp ((H : ℝ) * T * (((A : ℝ) * a + B * b) / 2)) := by
    dsimp only [R, S, H]
    convert hp using 1
    congr 1
    ring
  have hdecay := degree_margin_cost A B a b σ τ T hσ.le hτ.le hT.le hmargin
  have hC : 0 ≤ constant A B := (constant_positive A B).le
  calc
    _ ≤ (S * constant A B * Real.exp (-lowerCost H (σ * T) (τ * T))) * R :=
      mul_le_mul_of_nonneg_right hd hR
    _ = (R * S) * constant A B * Real.exp (-lowerCost H (σ * T) (τ * T)) := by ring
    _ ≤ Real.exp ((H : ℝ) * T * (((A : ℝ) * a + B * b) / 2)) * constant A B *
        Real.exp (-lowerCost H (σ * T) (τ * T)) := by gcongr
    _ = constant A B * Real.exp ((H : ℝ) * T * (((A : ℝ) * a + B * b) / 2) -
        lowerCost H (σ * T) (τ * T)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ constant A B * Real.exp (-((H : ℝ) * T)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdecay) hC
    _ ≤ constant A B * Real.exp (-T) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith only [hH, hT]
    _ < 1 := hconstant

end PaperP1.DeterminantStrictMargin
