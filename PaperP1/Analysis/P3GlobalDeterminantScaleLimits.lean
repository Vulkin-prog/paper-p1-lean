module

public import PaperP1.Analysis.P3StandardMonomialLimits
public import Mathlib.Analysis.Real.Sqrt

/-! # Actual global surface determinant scales and their error terms have proved leading limits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GlobalDeterminantScaleLimits

open Filter Topology P3StandardMonomialParameters

theorem sqrt_size_ratio (d : ℕ) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun e : ℕ ↦ Real.sqrt (2 * (size d e : ℝ) / D) / (e : ℝ)) atTop
      (𝓝 (Real.sqrt ((d : ℝ) / D))) := by
  have h := ((P3StandardMonomialLimits.size_ratio d).mul_const (2 / D)).sqrt
  have hc : ((d : ℝ) / 2) * (2 / D) = (d : ℝ) / D := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have ha : ((size d e : ℝ) / (e : ℝ) ^ 2) * (2 / D) =
      (2 * (size d e : ℝ) / D) / (e : ℝ) ^ 2 := by field_simp [he0, hD.ne']
  rw [ha, Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg e)]

theorem main_scale_ratio (d : ℕ) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun e : ℕ ↦ Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) / (e : ℝ) ^ 3)
      atTop (𝓝 (Real.sqrt ((d : ℝ) / D) * ((d : ℝ) / 2))) := by
  have h := (sqrt_size_ratio d D hD).mul (P3StandardMonomialLimits.size_ratio d)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  change (Real.sqrt (2 * (size d e : ℝ) / D) / (e : ℝ)) *
    ((size d e : ℝ) / (e : ℝ) ^ 2) = _
  field_simp [he0]

theorem constant_error_ratio (d : ℕ) (D C : ℝ) (hD : 0 < D) :
    Tendsto (fun e : ℕ ↦ C * Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) /
      ((e : ℝ) ^ 3 * Real.log (e : ℝ))) atTop (𝓝 0) := by
  have hi : Tendsto (fun e : ℕ ↦ (Real.log (e : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (main_scale_ratio d D hD).mul (hi.const_mul C)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hl0 : Real.log (e : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < e by omega))).ne'
  change (Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) / (e : ℝ) ^ 3) *
    (C * (Real.log (e : ℝ))⁻¹) = _
  field_simp [he0, hl0]

theorem theta_error_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ 3 * (size d e : ℝ) * (e : ℝ) * Real.log 4 /
      ((e : ℝ) ^ 3 * Real.log (e : ℝ))) atTop (𝓝 0) := by
  have hi : Tendsto (fun e : ℕ ↦ (Real.log (e : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (P3StandardMonomialLimits.size_ratio d).mul (hi.const_mul (3 * Real.log 4))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hl0 : Real.log (e : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < e by omega))).ne'
  change ((size d e : ℝ) / (e : ℝ) ^ 2) * ((3 * Real.log 4) * (Real.log (e : ℝ))⁻¹) = _
  field_simp [he0, hl0]

end PaperP1.P3GlobalDeterminantScaleLimits
