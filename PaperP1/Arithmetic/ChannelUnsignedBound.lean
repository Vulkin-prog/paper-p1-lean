module

public import PaperP1.Arithmetic.ChannelWordHosts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A direct finite upper bound on the positive channel sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelUnsignedBound

open Finset PaperP1.ChannelPlacements PaperP1.ChannelSumIdentity

theorem weight_sum_le (m : ℕ) : (∑ d ∈ Icc 1 m, weight d) ≤ (2 : ℤ) ^ m := by
  by_cases hm : m = 0
  · subst m
    norm_num
  · have hsum : (∑ d ∈ Icc 1 m, weight d) = moment m 0 := by
      simp only [moment, pow_zero, mul_one, positive_interval_sum]
    rw [hsum, (moments (by omega : 1 ≤ m)).1]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (Nat.sub_le m 1)

theorem placement_card_le (L D : ℕ) : (placements L D).card ≤ L + 1 := by
  unfold placements
  split
  · simp only [card_range]
    exact Nat.sub_le _ _
  · simp only [card_empty]
    omega

theorem unsigned_upper {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    unsigned L a b ≤ ((L + 1 : ℕ) : ℤ) ^ 2 * (2 : ℤ) ^ (L / b) := by
  rw [← unsigned_pair_sum_eq hb hab]
  unfold unsignedPairSum
  calc
    _ ≤ ∑ d ∈ Icc 1 (L / b), weight d * ((L + 1 : ℕ) : ℤ) ^ 2 := by
      apply sum_le_sum
      intro d _
      have hw : (0 : ℤ) ≤ weight d := by unfold weight; split <;> positivity
      have h₁ : ((placements L (a * d)).card : ℤ) ≤ ((L + 1 : ℕ) : ℤ) := by exact_mod_cast placement_card_le L (a * d)
      have h₂ : ((placements L (b * d)).card : ℤ) ≤ ((L + 1 : ℕ) : ℤ) := by exact_mod_cast placement_card_le L (b * d)
      have hprod := mul_le_mul h₁ h₂ (Nat.cast_nonneg (α := ℤ) _) (Nat.cast_nonneg (α := ℤ) (L + 1))
      have hmul := mul_le_mul_of_nonneg_left hprod hw
      nlinarith only [hmul]
    _ = ((L + 1 : ℕ) : ℤ) ^ 2 * (∑ d ∈ Icc 1 (L / b), weight d) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weight_sum_le (L / b)) (sq_nonneg _)

theorem unsigned_upper_rpow {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    ((unsigned L a b : ℤ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 2 *
      (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  have hbase : ((unsigned L a b : ℤ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (L / b) := by
    exact_mod_cast unsigned_upper (L := L) hb hab
  have hdiv : ((L / b : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b := by
    apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).mpr
    have hnat : L / b * b ≤ L + 1 := (Nat.div_mul_le_self L b).trans (Nat.le_succ L)
    exact_mod_cast hnat
  have hp : (2 : ℝ) ^ (L / b) ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv
  exact hbase.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg _))

end PaperP1.ChannelUnsignedBound
