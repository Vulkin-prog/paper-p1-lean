module

public import PaperP1.Analysis.EffectiveSourceCoordinates
public import PaperP1.Analysis.RelativeIntervalLattice

/-! # The coefficient-scaled quadratic grid yields a uniformly bounded actual lattice box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VerticalGridLattice

open PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum

theorem center_identity (M q : ℕ) (hM : 0 < M) {C U V : ℝ}
    (hC : C ≠ 0) (hU : U ≠ 0) :
    intervalCenter (2 * M) (2 * C * V) (C * U) q = (V / U) * ((q : ℝ) / M) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold intervalCenter
  push_cast
  field_simp

theorem point_box (M q : ℕ) (hM : 0 < M) {C U V K : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hV : 0 < V) (hK : 1 ≤ K)
    (z : Fin 2 → ℤ) (hu : 0 < (z 1 : ℝ)) (huhi : (z 1 : ℝ) ≤ 2 * C * U)
    (herr : |(z 0 : ℝ) / (z 1 : ℝ) - (V / U) * ((q : ℝ) / M)| ≤ (V / U) * K / M) :
    ∀ i, |realImage (transform (2 * C * V) (C * U) (2 * M)
      (intervalCenter (2 * M) (2 * C * V) (C * U) q)) z i| ≤ 2 * K := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : ((2 * M : ℝ) / (2 * C * V)) *
      ((z 0 : ℝ) - ((V / U) * ((q : ℝ) / M)) * (z 1 : ℝ)) =
      ((M : ℝ) / (C * V) * (z 1 : ℝ)) *
        ((z 0 : ℝ) / (z 1 : ℝ) - (V / U) * ((q : ℝ) / M)) := by
    field_simp
  have hcoef : 0 ≤ (M : ℝ) / (C * V) * (z 1 : ℝ) := by positivity
  have hcancel : ((M : ℝ) / (C * V) * (z 1 : ℝ)) * ((V / U) * K / M) =
      (z 1 : ℝ) * K / (C * U) := by field_simp
  have hfirst : |((M : ℝ) / (C * V) * (z 1 : ℝ)) *
      ((z 0 : ℝ) / (z 1 : ℝ) - (V / U) * ((q : ℝ) / M))| ≤ 2 * K := by
    rw [abs_mul, abs_of_nonneg hcoef]
    calc
      _ ≤ ((M : ℝ) / (C * V) * (z 1 : ℝ)) * ((V / U) * K / M) :=
        mul_le_mul_of_nonneg_left herr hcoef
      _ = (z 1 : ℝ) * K / (C * U) := hcancel
      _ ≤ 2 * K := (div_le_iff₀ (mul_pos hC hU)).mpr (by nlinarith)
  intro i
  rw [image_formula]
  fin_cases i
  · change |((2 * M : ℝ) / (2 * C * V)) *
      ((z 0 : ℝ) - intervalCenter (2 * M) (2 * C * V) (C * U) q * (z 1 : ℝ))| ≤ 2 * K
    rw [center_identity M q hM hC.ne' hU.ne', heq]
    exact hfirst
  · change |(z 1 : ℝ) / (C * U)| ≤ 2 * K
    rw [abs_of_pos (div_pos hu (mul_pos hC hU))]
    have ht : (z 1 : ℝ) / (C * U) ≤ 2 := (div_le_iff₀ (mul_pos hC hU)).mpr (by nlinarith only [huhi])
    linarith

end PaperP1.VerticalGridLattice
