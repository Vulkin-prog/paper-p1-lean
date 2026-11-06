module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfaceAuxiliaryDegreeChoice

def degree (E₀ H : ℕ) (β : ℝ) : ℕ := E₀ + ⌈(H : ℝ) ^ β⌉₊

theorem minimum_le (E₀ H : ℕ) (β : ℝ) : E₀ ≤ degree E₀ H β := Nat.le_add_right _ _

theorem power_le (E₀ H : ℕ) (β : ℝ) : (H : ℝ) ^ β ≤ (degree E₀ H β : ℝ) := by
  have hh := Nat.le_ceil ((H : ℝ) ^ β)
  change (H : ℝ) ^ β ≤ ((E₀ + ⌈(H : ℝ) ^ β⌉₊ : ℕ) : ℝ)
  rw [Nat.cast_add]
  linarith [(Nat.cast_nonneg E₀ : (0 : ℝ) ≤ E₀)]

theorem degree_bound (E₀ H : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hH : 1 ≤ H) :
    (degree E₀ H β : ℝ) ≤ ((E₀ + 2 : ℕ) : ℝ) * (H : ℝ) ^ β := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp : 1 ≤ (H : ℝ) ^ β := Real.one_le_rpow hHR hβ
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg H) β)
  have hm := mul_nonneg (Nat.cast_nonneg E₀ : (0 : ℝ) ≤ E₀) (sub_nonneg.mpr hp)
  simp only [degree, Nat.cast_add, Nat.cast_ofNat]
  nlinarith

theorem log_height_bound (E₀ H : ℕ) (β : ℝ) (hβ : 0 < β) (hH : 1 ≤ H) :
    Real.log (H : ℝ) ≤ (1 / β) * Real.log (degree E₀ H β : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hp := Real.rpow_pos_of_pos hHR β
  have hl := Real.log_le_log hp (power_le E₀ H β)
  rw [Real.log_rpow hHR β] at hl
  have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hβ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul, one_div] using hh

theorem reciprocal_margin (d : ℕ) (hd : 0 < d) (D β : ℝ) (hD : 0 < D) (hβ : 0 < β)
    (hmargin : Real.sqrt (D / (d : ℝ)) < β) : 1 / β < Real.sqrt ((d : ℝ) / D) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  rw [Real.sqrt_div hD.le] at hmargin
  rw [Real.sqrt_div hdR.le, div_lt_div_iff₀ hβ hsD]
  have hh := (div_lt_iff₀ hsd).mp hmargin
  simpa only [one_mul, mul_comm] using hh

end PaperP1.SurfaceAuxiliaryDegreeChoice
