module

public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Asymptotics.CoarseFixedFactorialMomentsUnderBCN

/-! # A first vanishing bound for the actual fourth factorial cumulant under BCN

The complete finite heterogeneous identity is proved independently. This
coarse estimate does not assert the source connected-quartic comparison.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseFourthCumulantUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.FourthRunFactorialCumulant PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum

theorem uniform_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |fourthFactorialCumulant (dyadicBlock N) L| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := min (ε / 2) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1 / 4 := min_le_right _ _
  have hηeps : η ≤ ε / 2 := min_le_left _ _
  have hloss : 0 < ε - η := by linarith only [hε, hηeps]
  obtain ⟨N2, _hN2, h2⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_actual_error 2 c κ hc hBCN C η hη
  obtain ⟨N3, _hN3, h3⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_actual_error 3 c κ hc hBCN C η hη
  obtain ⟨N4, _hN4, h4⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_actual_error 4 c κ hc hBCN C η hη
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (4 + 4 * M + 6 * M ^ 2) (-1 / 2 + η) (ε - η) hloss
  refine ⟨max NM (max N2 (max N3 (max N4 NF))), by omega, ?_⟩
  intro N hN L hband
  let μ := actualMean (dyadicBlock N) L
  let d := fun r ↦ factorialCountMoment (dyadicBlock N) L r - μ ^ r
  let T := (N : ℝ) ^ (-1 / 2 + η)
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hm : μ ≤ M := by
    dsimp only [μ]
    rw [actualMean_eq_countMoment (subset_refl _)]
    exact (hmean N (by omega) L hband).2
  have hM : 0 ≤ M := hμ.trans hm
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hTone : T ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηsmall] : -1 / 2 + η ≤ 0)
  have hd2 : |d 2| ≤ T := h2 N (by omega) L hband
  have hd3 : |d 3| ≤ T := h3 N (by omega) L hband
  have hd4 : |d 4| ≤ T := h4 N (by omega) L hband
  have hdsq : (d 2) ^ 2 ≤ T := by
    have hp := pow_le_pow_left₀ (abs_nonneg (d 2)) hd2 2
    rw [sq_abs] at hp
    nlinarith only [hp, hT, hTone]
  have hid : fourthFactorialCumulant (dyadicBlock N) L = d 4 - 4 * μ * d 3 + 6 * μ ^ 2 * d 2 - 3 * (d 2) ^ 2 := by
    rw [fourthFactorialCumulant, factorialCountMoment_one,
      ← actualMean_eq_countMoment (subset_refl _)]
    dsimp [d, μ]
    ring
  have ha : |fourthFactorialCumulant (dyadicBlock N) L| ≤
      |d 4| + 4 * μ * |d 3| + 6 * μ ^ 2 * |d 2| + 3 * (d 2) ^ 2 := by
    rw [hid]
    have h1 := abs_sub (d 4 - 4 * μ * d 3 + 6 * μ ^ 2 * d 2) (3 * (d 2) ^ 2)
    have h2 := abs_add_le (d 4 - 4 * μ * d 3) (6 * μ ^ 2 * d 2)
    have h3 := abs_sub (d 4) (4 * μ * d 3)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * μ)] at h3
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * μ ^ 2)] at h2
    rw [abs_of_nonneg (by positivity : 0 ≤ 3 * (d 2) ^ 2)] at h1
    linarith only [h1, h2, h3]
  have hp3 := mul_le_mul_of_nonneg_left hd3 (by positivity : 0 ≤ 4 * μ)
  have hp2 := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ 6 * μ ^ 2)
  have hm1 := mul_le_mul_of_nonneg_right hm hT
  have hm2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hμ hm 2) hT
  calc
    _ ≤ (4 + 4 * M + 6 * M ^ 2) * T := by linarith only [ha, hd4, hp3, hp2, hm1, hm2, hdsq]
    _ ≤ (N : ℝ) ^ ((-1 / 2 + η) + (ε - η)) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CoarseFourthCumulantUnderBCN
