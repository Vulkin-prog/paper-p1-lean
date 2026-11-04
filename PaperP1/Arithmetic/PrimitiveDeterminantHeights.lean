module

public import PaperP1.Arithmetic.DeterminantPrimitiveReduction

/-! # Primitive reduction preserves coefficient heights at the reduced source scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveDeterminantHeights

open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantPrimitiveReduction

theorem left_quotient (c : ℕ) (a : Quad) (hs : 0 < scale a) :
    (c * a.1.1 ^ 2 * a.2.1) / scale a = c * (reduced a).1.1 ^ 2 * (reduced a).2.1 := by
  have hd : scale a ∣ c * a.1.1 ^ 2 * a.2.1 := ⟨_, left_factor c a⟩
  exact mul_left_cancel₀ hs.ne' ((Nat.mul_div_cancel' hd).trans (left_factor c a))

theorem right_quotient (c : ℕ) (a : Quad) (hs : 0 < scale a) :
    (c * a.1.2 ^ 2 * a.2.2) / scale a = c * (reduced a).1.2 ^ 2 * (reduced a).2.2 := by
  have hd : scale a ∣ c * a.1.2 ^ 2 * a.2.2 := ⟨_, right_factor c a⟩
  exact mul_left_cancel₀ hs.ne' ((Nat.mul_div_cancel' hd).trans (right_factor c a))

theorem left_coefficient_bound (c : ℕ) (a : Quad)
    (hd : 0 < a.1.1) (he : 0 < a.1.2) (hu : 0 < a.2.1) (hv : 0 < a.2.2) :
    scale a * c ≤ c * a.1.1 ^ 2 * a.2.1 := by
  have hp := primitive a hd he hu hv
  have hc : c ≤ c * (reduced a).1.1 ^ 2 * (reduced a).2.1 :=
    (Nat.le_mul_of_pos_right c (pow_pos hp.2.1 _)).trans
      (Nat.le_mul_of_pos_right _ hp.2.2.2.1)
  rw [left_factor]
  exact Nat.mul_le_mul_left _ hc

theorem right_coefficient_bound (c : ℕ) (a : Quad)
    (hd : 0 < a.1.1) (he : 0 < a.1.2) (hu : 0 < a.2.1) (hv : 0 < a.2.2) :
    scale a * c ≤ c * a.1.2 ^ 2 * a.2.2 := by
  have hp := primitive a hd he hu hv
  have hc : c ≤ c * (reduced a).1.2 ^ 2 * (reduced a).2.2 :=
    (Nat.le_mul_of_pos_right c (pow_pos hp.2.2.1 _)).trans
      (Nat.le_mul_of_pos_right _ hp.2.2.2.2.1)
  rw [right_factor]
  exact Nat.mul_le_mul_left _ hc

theorem left_height_transfer (c : ℕ) (a : Quad)
    (hd : 0 < a.1.1) (he : 0 < a.1.2) (hu : 0 < a.2.1) (hv : 0 < a.2.2)
    (C N : ℝ) (hheight : ((c * a.1.1 ^ 2 * a.2.1 : ℕ) : ℝ) ≤ C * N) :
    (c : ℝ) ≤ C * (N / scale a) := by
  have hs : (0 : ℝ) < scale a := by exact_mod_cast (primitive a hd he hu hv).1
  have hc : (scale a : ℝ) * c ≤ ((c * a.1.1 ^ 2 * a.2.1 : ℕ) : ℝ) := by
    exact_mod_cast left_coefficient_bound c a hd he hu hv
  calc
    _ ≤ ((c * a.1.1 ^ 2 * a.2.1 : ℕ) : ℝ) / scale a :=
      (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hc)
    _ ≤ (C * N) / scale a := div_le_div_of_nonneg_right hheight hs.le
    _ = _ := by ring

theorem right_height_transfer (c : ℕ) (a : Quad)
    (hd : 0 < a.1.1) (he : 0 < a.1.2) (hu : 0 < a.2.1) (hv : 0 < a.2.2)
    (C N : ℝ) (hheight : ((c * a.1.2 ^ 2 * a.2.2 : ℕ) : ℝ) ≤ C * N) :
    (c : ℝ) ≤ C * (N / scale a) := by
  have hs : (0 : ℝ) < scale a := by exact_mod_cast (primitive a hd he hu hv).1
  have hc : (scale a : ℝ) * c ≤ ((c * a.1.2 ^ 2 * a.2.2 : ℕ) : ℝ) := by
    exact_mod_cast right_coefficient_bound c a hd he hu hv
  calc
    _ ≤ ((c * a.1.2 ^ 2 * a.2.2 : ℕ) : ℝ) / scale a :=
      (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hc)
    _ ≤ (C * N) / scale a := div_le_div_of_nonneg_right hheight hs.le
    _ = _ := by ring

end PaperP1.PrimitiveDeterminantHeights
