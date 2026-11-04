module

public import PaperP1.Arithmetic.ReciprocalOddPivots
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Literal natural quotient geometry on the small square-part range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquarePartLogGeometry

theorem quotient_bounds {X a : ℕ} (ha : 0 < a) (hsquare : a ^ 2 ≤ X) :
    0 < X / a ^ 2 ∧ (X : ℝ) / (2 * (a : ℝ) ^ 2) ≤ ((X / a ^ 2 : ℕ) : ℝ) ∧
      ((X / a ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / (a : ℝ) ^ 2 := by
  have hq : 1 ≤ X / a ^ 2 := (Nat.le_div_iff_mul_le (pow_pos ha 2)).mpr (by simpa only [one_mul] using hsquare)
  have hqr : (1 : ℝ) ≤ ((X / a ^ 2 : ℕ) : ℝ) := by exact_mod_cast hq
  have hless : (X : ℝ) < (a : ℝ) ^ 2 * (((X / a ^ 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ X (pow_pos ha 2)
  refine ⟨by omega, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (a : ℝ) ^ 2)).mpr
    have hm := mul_nonneg (sq_nonneg (a : ℝ)) (sub_nonneg.mpr hqr)
    nlinarith only [hless, hm]
  · have hh : ((X / a ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((a ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
    rwa [Nat.cast_pow] at hh

theorem log_quotient_range {X a : ℕ} {V : ℝ} (ha : 0 < a) (hsquare : a ^ 2 ≤ X)
    (haexp : (a : ℝ) ≤ Real.exp (4 * V)) (hV : Real.log 2 ≤ V) :
    Real.log X - 9 * V ≤ Real.log ((X / a ^ 2 : ℕ) : ℝ) ∧
      Real.log ((X / a ^ 2 : ℕ) : ℝ) ≤ Real.log X := by
  obtain ⟨hq, hlo, _hhi⟩ := quotient_bounds ha hsquare
  have hX : 0 < X := (pow_pos ha 2).trans_le hsquare
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hqr : (0 : ℝ) < ((X / a ^ 2 : ℕ) : ℝ) := by exact_mod_cast hq
  have hlower := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ) / (2 * (a : ℝ) ^ 2)) hlo
  have hloga : Real.log (a : ℝ) ≤ 4 * V := by
    simpa only [Real.log_exp] using Real.log_le_log har haexp
  rw [Real.log_div hXr.ne' (by positivity : (2 * (a : ℝ) ^ 2) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (a : ℝ) ^ 2 ≠ 0),
    Real.log_pow] at hlower
  refine ⟨by linarith only [hlower, hloga, hV], ?_⟩
  exact Real.log_le_log hqr (by exact_mod_cast Nat.div_le_self X (a ^ 2))

end PaperP1.SquarePartLogGeometry
