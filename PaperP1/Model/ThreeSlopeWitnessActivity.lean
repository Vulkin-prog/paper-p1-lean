module

public import PaperP1.Model.ThreeSlopeWitnessMass
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Model.TripleActivityConnected

/-! # Exact centered activity and positive connectedness of the rational witness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopeWitnessActivity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ThreeSlopeProgressions PaperP1.ThreeSlopeValueCounts PaperP1.ThreeSlopeWitnessMass
  PaperP1.PrivateNormalizedFamilies

theorem centered_formula {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteCenteredCoefficient L (support t) = ((2 ^ L : ℝ)⁻¹) ^ 3 *
      ((2 ^ nullity L : ℝ) - 2 ^ pairFloor L 6 - 2 ^ pairFloor L 3 - 2 ^ pairFloor L 5 + 2) := by
  have hne01 : centres t 0 ≠ centres t 1 := fun hh ↦ (by decide : (0 : Fin 3) ≠ 1) (centres_injective ht hh)
  have hne02 : centres t 0 ≠ centres t 2 := fun hh ↦ (by decide : (0 : Fin 3) ≠ 2) (centres_injective ht hh)
  have hne12 : centres t 1 ≠ centres t 2 := fun hh ↦ (by decide : (1 : Fin 3) ≠ 2) (centres_injective ht hh)
  have hs : support t = {centres t 0, centres t 1, centres t 2} := by rw [support_eq]; rfl
  have hh := InfiniteTripleCancellation.normalized L hne01 hne02 hne12
  rw [← hs, joint_probability ht hL hprivate, pair_zero_one_probability ht hL hprivate,
    pair_zero_two_probability ht hL hprivate, pair_one_two_probability ht hL hprivate,
    marginals ht hL hprivate 0, marginals ht hL hprivate 1, marginals ht hL hprivate 2] at hh
  rw [hh]
  ring

theorem floor_gap (L : ℕ) (hL : 60 ≤ L) :
    pairFloor L 6 ≤ pairFloor L 3 ∧ pairFloor L 5 ≤ pairFloor L 3 ∧ pairFloor L 3 + 3 ≤ nullity L := by
  unfold nullity pairFloor
  omega

theorem polynomial_lower (L : ℕ) (hL : 60 ≤ L) :
    (2 ^ nullity L : ℝ) / 2 ≤
      (2 ^ nullity L : ℝ) - 2 ^ pairFloor L 6 - 2 ^ pairFloor L 3 - 2 ^ pairFloor L 5 + 2 := by
  obtain ⟨h6, h5, hgap⟩ := floor_gap L hL
  have hp6 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h6
  have hp5 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h5
  have hpg := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hgap
  rw [pow_add] at hpg
  norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num] at hpg
  have hb : 0 ≤ (2 ^ pairFloor L 3 : ℝ) := by positivity
  linarith only [hp6, hp5, hpg, hb]

theorem half_joint_lower {t L : ℕ} (ht : 1 ≤ t) (hL : 60 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteJointMoment L (support t) / 2 ≤ infiniteCenteredCoefficient L (support t) := by
  rw [joint_probability ht (by omega) hprivate, centered_formula ht (by omega) hprivate]
  have hh := mul_le_mul_of_nonneg_left (polynomial_lower L hL)
    (by positivity : (0 : ℝ) ≤ ((2 ^ L : ℝ)⁻¹) ^ 3)
  linarith only [hh]

theorem centered_positive {t L : ℕ} (ht : 1 ≤ t) (hL : 60 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    0 < infiniteCenteredCoefficient L (support t) := by
  have hpos : 0 < infiniteJointMoment L (support t) := by
    rw [joint_probability ht (by omega) hprivate]
    positivity
  exact (div_pos hpos (by norm_num)).trans_le (half_joint_lower ht hL hprivate)

theorem connected {t L : ℕ} (ht : 1 ≤ t) (hL : 60 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    ConnectedWindowFamilies.Connected L (support t) := by
  apply TripleActivityConnected.connected_of_coefficient_ne_zero L (by omega) (support t) (support_card ht)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
    rw [marginals ht (by omega) hprivate i]
    positivity
  · exact (centered_positive ht hL hprivate).ne'

end PaperP1.ThreeSlopeWitnessActivity
