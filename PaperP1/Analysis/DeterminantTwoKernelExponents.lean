module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Exact optimization of the two determinant exponents, including a uniform perturbation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantTwoKernelExponents

def first (z w : ℝ) : ℝ := z / 2 + (9 / 8 : ℝ) * z * (w - z)

def second (z w : ℝ) : ℝ := w - z + (9 / 8 : ℝ) * z * (w - z)

def maximum (w : ℝ) : ℝ := w / 3 + w ^ 2 / 4

theorem at_crossing (w : ℝ) : first (2 * w / 3) w = maximum w ∧
    second (2 * w / 3) w = maximum w := by
  constructor
  · unfold first maximum; ring
  · unfold second maximum; ring

theorem min_le_maximum (z w : ℝ) (hw : 0 ≤ w) (hhigh : w ≤ 4 / 3) :
    min (first z w) (second z w) ≤ maximum w := by
  by_cases hz : z ≤ 2 * w / 3
  · have hfactor : 0 ≤ 1 / 2 + 3 * w / 8 - 9 * z / 8 := by linarith only [hz, hhigh]
    have hh := mul_nonneg (sub_nonneg.mpr hz) hfactor
    exact (min_le_left _ _).trans (by unfold first maximum; nlinarith only [hh])
  · have hfactor : 0 ≤ 1 - 3 * w / 8 + 9 * z / 8 := by linarith only [hw, hz]
    have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hz)) hfactor
    exact (min_le_right _ _).trans (by unfold second maximum; nlinarith only [hh])

theorem maximum_monotone {w v : ℝ} (hw : 0 ≤ w) (hwv : w ≤ v) : maximum w ≤ maximum v := by
  have hh := mul_nonneg (sub_nonneg.mpr hwv) (by linarith : 0 ≤ v + w)
  unfold maximum
  nlinarith only [hh, hwv]

theorem seven_twelfths (z w : ℝ) (hw : 0 ≤ w) (hhigh : w ≤ 1) :
    min (first z w) (second z w) ≤ 7 / 12 := by
  have hm := min_le_maximum z w hw (by linarith only [hhigh])
  have hp := maximum_monotone hw hhigh
  norm_num [maximum] at hp
  exact hm.trans hp

theorem perturbed_seven_twelfths (z w η : ℝ) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 3)
    (hw : 0 ≤ w) (hhigh : w ≤ 1 + η) :
    min (first z w) (second z w) ≤ 7 / 12 + η := by
  have hm := min_le_maximum z w hw (by linarith only [hhigh, hηsmall])
  have hp := maximum_monotone hw hhigh
  have hh := mul_nonneg hη (by linarith only [hηsmall] : 0 ≤ 2 / 3 - η)
  unfold maximum at hm hp
  nlinarith only [hm, hp, hh]

theorem min_power_bound {N : ℝ} (hN : 1 ≤ N) (z w η : ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 3) (hw : 0 ≤ w) (hhigh : w ≤ 1 + η) :
    min (N ^ first z w) (N ^ second z w) ≤ N ^ (7 / 12 + η) := by
  by_cases he : first z w ≤ second z w
  · have hp : first z w ≤ 7 / 12 + η := by
      simpa only [min_eq_left he] using perturbed_seven_twelfths z w η hη hηsmall hw hhigh
    exact (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_le hN hp)
  · have hp : second z w ≤ 7 / 12 + η := by
      simpa only [min_eq_right (le_of_not_ge he)] using perturbed_seven_twelfths z w η hη hηsmall hw hhigh
    exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_le hN hp)

end PaperP1.DeterminantTwoKernelExponents
