module

public import PaperP1.Analysis.RealSeriesEvaluation
public import Mathlib.Tactic.Linarith

/-! # An explicit geometric bound on the tail beyond the constant coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealSeriesTail

open PaperP1.RealSeriesEvaluation

theorem geometric_tail (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1) :
    (∑' n : ℕ, r ^ (n + 1)) = r / (1 - r) := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr hr₁]
  ring

theorem constant_tail (f : PowerSeries ℚ) (t r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1)
    (hzero : PowerSeries.coeff 0 f = 1) (hterm : ∀ n, ‖term f t n‖ ≤ r ^ n) :
    |value f t - 1| ≤ r / (1 - r) := by
  have hgeo := summable_geometric_of_lt_one hr hr₁
  have hnorm : AbsolutelySummable f t :=
    hgeo.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hnormTail : Summable (fun n ↦ ‖term f t (n + 1)‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  have hgeoTail : Summable (fun n : ℕ ↦ r ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  have hvalue := hnorm.of_norm.tsum_eq_zero_add
  change value f t = term f t 0 + ∑' n, term f t (n + 1) at hvalue
  have hconstant : term f t 0 = 1 := by simp only [term, hzero, Rat.cast_one, pow_zero, mul_one]
  have hrest : value f t - 1 = ∑' n, term f t (n + 1) := by rw [hvalue, hconstant]; ring
  rw [hrest, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnormTail).trans
    ((Summable.tsum_le_tsum (fun n ↦ hterm (n + 1)) hnormTail hgeoTail).trans_eq (geometric_tail r hr hr₁))

end PaperP1.RealSeriesTail
