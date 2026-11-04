module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Factoring the clean-pair collision term before using a reciprocal lower bound

The main reciprocal term and its collision loss must be combined before
substituting a lower bound. Bounding those terms separately loses the
small-pivot lower estimate.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.CleanPairReciprocalLower

theorem factor_identity (n s j c z : ℝ) :
    n * s - j - c * ((n / z) * s + j) = (1 - c / z) * n * s - (c + 1) * j := by
  simp only [div_eq_mul_inv]
  ring

theorem substitute_lower {n s j c z Q : ℝ} (hn : 0 ≤ n) (hz : 0 < z) (hc : c ≤ z)
    (hs : j / Q ≤ s) :
    (1 - c / z) * n * (j / Q) - (c + 1) * j ≤ n * s - j - c * ((n / z) * s + j) := by
  rw [factor_identity]
  have hcoef : 0 ≤ 1 - c / z := sub_nonneg.mpr ((div_le_one hz).mpr hc)
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hs (mul_nonneg hcoef hn)) _

end PaperP1.CleanPairReciprocalLower
