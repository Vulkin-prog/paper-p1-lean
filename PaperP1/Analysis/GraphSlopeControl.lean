module

public import PaperP1.Analysis.GradientComparisonControl
public import PaperP1.Analysis.BothGraphDerivativeFormulas

/-! # Actual unit-slope and distance bounds in a selected normalized orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphSlopeControl

open MvPolynomial Set GradientComparisonControl BothGraphDerivativeFormulas

theorem first_abs_deriv (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hconn : IsPreconnected s) (hφ : GraphTangentEvaluation.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (hinit : |eval (fun j ↦ φ j t₀) (pderiv 0 P)| ≤ |eval (fun j ↦ φ j t₀) (pderiv 1 P)|)
    (t : ℝ) (ht : t ∈ s) : |deriv (φ 1) t| ≤ 1 := by
  have hcmp := abs_le_propagates P r s hconn (fun v ↦ fun j ↦ φ j v)
    (continuousOn_first P φ s hφ) hcurve t₀ ht₀ hinit t ht
  have hd : deriv (φ 1) t = -eval (fun j ↦ φ j t) (pderiv 0 P) /
      eval (fun j ↦ φ j t) (pderiv 1 P) := by
    simpa [GraphTangentEvaluation.velocity] using (hφ.2 t ht 1).deriv
  rw [hd, abs_div, abs_neg]
  exact (div_le_one (abs_pos.mpr (hφ.1 t ht))).mpr hcmp

theorem second_abs_deriv (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hconn : IsPreconnected s) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (hinit : |eval (fun j ↦ φ j t₀) (pderiv 1 P)| ≤ |eval (fun j ↦ φ j t₀) (pderiv 0 P)|)
    (t : ℝ) (ht : t ∈ s) : |deriv (φ 0) t| ≤ 1 := by
  have hcmp := abs_ge_propagates P r s hconn (fun v ↦ fun j ↦ φ j v)
    (continuousOn_second P φ s hφ) hcurve t₀ ht₀ hinit t ht
  have hd : deriv (φ 0) t = -eval (fun j ↦ φ j t) (pderiv 1 P) /
      eval (fun j ↦ φ j t) (pderiv 0 P) := by
    simpa [TransposedNormalizedGraphPiece.velocity] using (hφ.2 t ht 0).deriv
  rw [hd, abs_div, abs_neg]
  exact (div_le_one (abs_pos.mpr (hφ.1 t ht))).mpr hcmp

theorem first_distance (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : GraphTangentEvaluation.Trajectory P φ (Ioo a b))
    (hcurve : ∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hinit : |eval (fun j ↦ φ j t₀) (pderiv 0 P)| ≤ |eval (fun j ↦ φ j t₀) (pderiv 1 P)|)
    (t u : ℝ) (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) : |φ 1 t - φ 1 u| ≤ |t - u| := by
  have hbound : ∀ v ∈ Ioo a b, ‖deriv (φ 1) v‖ ≤ (1 : ℝ) := by
    intro v hv
    simpa only [Real.norm_eq_abs] using first_abs_deriv P r φ (Ioo a b) isPreconnected_Ioo
      hφ hcurve t₀ ht₀ hinit v hv
  have hh := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le
    (fun v hv ↦ (hφ.2 v hv 1).differentiableAt) hbound hu ht
  simpa only [Real.norm_eq_abs, one_mul] using hh

theorem second_distance (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (a b : ℝ) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ (Ioo a b))
    (hcurve : ∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hinit : |eval (fun j ↦ φ j t₀) (pderiv 1 P)| ≤ |eval (fun j ↦ φ j t₀) (pderiv 0 P)|)
    (t u : ℝ) (ht : t ∈ Ioo a b) (hu : u ∈ Ioo a b) : |φ 0 t - φ 0 u| ≤ |t - u| := by
  have hbound : ∀ v ∈ Ioo a b, ‖deriv (φ 0) v‖ ≤ (1 : ℝ) := by
    intro v hv
    simpa only [Real.norm_eq_abs] using second_abs_deriv P r φ (Ioo a b) isPreconnected_Ioo
      hφ hcurve t₀ ht₀ hinit v hv
  have hh := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le
    (fun v hv ↦ (hφ.2 v hv 0).differentiableAt) hbound hu ht
  simpa only [Real.norm_eq_abs, one_mul] using hh

end PaperP1.GraphSlopeControl
