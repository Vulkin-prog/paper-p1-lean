module

public import PaperP1.Arithmetic.ChannelPhaseConstants

/-! # Exact height-five correction and the two source channel polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightFiveChannelCorrection

open Finset PaperP1.FiniteChannelHierarchy PaperP1.ChannelSumIdentity PaperP1.ChannelPhaseConstants

def correction (N L : ℕ) : ℝ := (nominalMean N L) ^ 2 / N * heightSum 5 L

theorem truncatedSum_succ (h L : ℕ) (hh : 3 ≤ h + 1) :
    truncatedSum (h + 1) L = truncatedSum h L + heightSum (h + 1) L :=
  sum_Icc_succ_top hh (fun b ↦ heightSum b L)

theorem coefficient_succ (N L h : ℕ) (hh : 3 ≤ h + 1) :
    coefficient N L (h + 1) = coefficient N L h + (nominalMean N L) ^ 2 / N * heightSum (h + 1) L := by
  rw [coefficient, truncatedSum_succ h L hh, mul_add]
  rfl

theorem heightSum_five (L : ℕ) :
    heightSum 5 L = (2 / 15 : ℝ) * (signed L 3 5 : ℝ) + (3 / 10 : ℝ) * (signed L 4 5 : ℝ) := by
  rw [heightSum, numerators_five, sum_pair (by decide)]
  norm_num [FiniteChannelHierarchy.weight_formula]

theorem coefficient_five (N L : ℕ) : coefficient N L 5 = coefficient N L 4 + correction N L :=
  coefficient_succ N L 4 (by decide)

theorem signed_three_five {q r : ℕ} (hq : 1 ≤ q) (hr : r < 5) :
    signed (5 * q + r) 3 5 = (2 : ℤ) ^ (q - 1) *
      (2 * ((r : ℤ) + 4) * q + (r : ℤ) ^ 2 + 6 * r + 38) - 8 * (5 * q + r : ℕ) - 7 := by
  have hdiv : (5 * q + r) / 5 = q := by omega
  unfold signed
  rw [hdiv, channel_identity hq _ _ _ (r : ℤ) _ (by push_cast; ring)]
  push_cast
  ring

theorem signed_four_five {q r : ℕ} (hq : 1 ≤ q) (hr : r < 5) :
    signed (5 * q + r) 4 5 = (2 : ℤ) ^ (q - 1) *
      (((r : ℤ) + 4) * q + (r : ℤ) ^ 2 + 7 * r + 52) - 9 * (5 * q + r : ℕ) - 11 := by
  have hdiv : (5 * q + r) / 5 = q := by omega
  unfold signed
  rw [hdiv, channel_identity hq _ _ _ (r : ℤ) _ (by push_cast; ring)]
  push_cast
  ring

theorem heightSum_five_closed {q r : ℕ} (hq : 1 ≤ q) (hr : r < 5) :
    heightSum 5 (5 * q + r) = (1 / 30 : ℝ) *
      ((2 : ℝ) ^ (q - 1) * (17 * ((r : ℝ) + 4) * q + 13 * (r : ℝ) ^ 2 + 87 * r + 620) -
        113 * ((5 * q + r : ℕ) : ℝ) - 127) := by
  rw [heightSum_five, signed_three_five hq hr, signed_four_five hq hr]
  push_cast
  ring

theorem correction_closed {N q r : ℕ} (hN : 0 < N) (hq : 1 ≤ q) (hr : r < 5) :
    correction N (5 * q + r) = (nominalMean N (5 * q + r)) ^ 2 / (30 * N) *
      ((2 : ℝ) ^ (q - 1) * (17 * ((r : ℝ) + 4) * q + 13 * (r : ℝ) ^ 2 + 87 * r + 620) -
        113 * ((5 * q + r : ℕ) : ℝ) - 127) := by
  rw [correction, heightSum_five_closed hq hr]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end PaperP1.HeightFiveChannelCorrection
