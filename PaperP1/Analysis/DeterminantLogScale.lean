module

public import PaperP1.Analysis.DeterminantRelativeChart
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Coefficient-uniform logarithmic determinant scale and exact denominator cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantLogScale

def logShape (N D E U V : ℝ) : ℝ := (9 / 8 : ℝ) * Real.log (D * E) * Real.log (U * V) / Real.log N

theorem denominator_cost {D E U V : ℝ} (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (A B : ℝ) :
    A * Real.log E + B * Real.log U + (A / 2) * Real.log (D / E) + (B / 2) * Real.log (V / U) =
      (A / 2) * Real.log (D * E) + (B / 2) * Real.log (U * V) := by
  rw [Real.log_div hD.ne' hE.ne', Real.log_div hV.ne' hU.ne',
    Real.log_mul hD.ne' hE.ne', Real.log_mul hU.ne' hV.ne']
  ring

theorem product_identity {c₁ c₂ D E U V : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V) :
    Real.log (U * V) = Real.log (c₁ * D ^ 2 * U) + Real.log (c₂ * E ^ 2 * V) -
      Real.log (c₁ * c₂) - 2 * Real.log (D * E) := by
  rw [Real.log_mul (mul_pos hc₁ (sq_pos_of_pos hD)).ne' hU.ne',
    Real.log_mul (mul_pos hc₂ (sq_pos_of_pos hE)).ne' hV.ne',
    Real.log_mul hc₁.ne' (pow_ne_zero 2 hD.ne'),
    Real.log_mul hc₂.ne' (pow_ne_zero 2 hE.ne'),
    Real.log_mul hc₁.ne' hc₂.ne', Real.log_mul hD.ne' hE.ne',
    Real.log_mul hU.ne' hV.ne', Real.log_pow, Real.log_pow]
  ring

theorem ideal_identity {N c₁ c₂ D E U V : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hfirst : c₁ * D ^ 2 * U = N) (hsecond : c₂ * E ^ 2 * V = N) :
    Real.log (U * V) = 2 * Real.log N - Real.log (c₁ * c₂) - 2 * Real.log (D * E) := by
  rw [product_identity hc₁ hc₂ hD hE hU hV, hfirst, hsecond]
  ring

theorem log_parameter_upper {N C c₁ c₂ D E U V : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hcoeff : 1 ≤ c₁ * c₂) (hfirst : c₁ * D ^ 2 * U ≤ C * N) (hsecond : c₂ * E ^ 2 * V ≤ C * N) :
    Real.log (U * V) ≤ 2 * Real.log N - 2 * Real.log (D * E) + 2 * Real.log C := by
  have hf := Real.log_le_log (mul_pos (mul_pos hc₁ (sq_pos_of_pos hD)) hU) hfirst
  have hs := Real.log_le_log (mul_pos (mul_pos hc₂ (sq_pos_of_pos hE)) hV) hsecond
  rw [Real.log_mul hC.ne' hN.ne'] at hf hs
  have hc := Real.log_nonneg hcoeff
  rw [product_identity hc₁ hc₂ hD hE hU hV]
  linarith only [hf, hs, hc]

theorem quadratic_shape_bound {A B H C : ℝ} (hH : 0 < H) (hA : 0 ≤ A)
    (hB : B ≤ 2 * H - 2 * A + C) :
    (9 / 8 : ℝ) * A * B / H ≤ (9 / 16 : ℝ) * H * (1 + C / (2 * H)) ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left hB hA
  have hs := sq_nonneg (2 * A - (H + C / 2))
  have hp : A * B ≤ (H + C / 2) ^ 2 / 2 := by nlinarith only [hh, hs]
  calc
    _ = (9 / 8 : ℝ) * (A * B / H) := by ring
    _ ≤ (9 / 8 : ℝ) * (((H + C / 2) ^ 2 / 2) / H) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hH.le) (by norm_num)
    _ = _ := by field_simp; ring

theorem shape_bound {N C c₁ c₂ D E U V : ℝ}
    (hN : 1 < N) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hcoeff : 1 ≤ c₁ * c₂) (hDE : 1 ≤ D * E)
    (hfirst : c₁ * D ^ 2 * U ≤ C * N) (hsecond : c₂ * E ^ 2 * V ≤ C * N) :
    logShape N D E U V ≤ (9 / 16 : ℝ) * Real.log N * (1 + Real.log C / Real.log N) ^ 2 := by
  have hh := quadratic_shape_bound (Real.log_pos hN) (Real.log_nonneg hDE)
    (log_parameter_upper (by linarith : 0 < N) hC hc₁ hc₂ hD hE hU hV hcoeff hfirst hsecond)
  have he : 2 * Real.log C / (2 * Real.log N) = Real.log C / Real.log N := by ring
  simpa only [logShape, he] using hh

end PaperP1.DeterminantLogScale
