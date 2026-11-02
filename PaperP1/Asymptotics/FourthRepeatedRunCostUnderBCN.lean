module

public import PaperP1.Model.FourthRunRemainder
public import PaperP1.Asymptotics.HalfPowerThirdActivityUnderBCN

/-! # All actual repeated-index corrections in the fourth cumulant cost N^(-3/2+epsilon)

This controls the exact remainder relative to unrestricted quartic activity
and the square of signed pair activity. The further connected-quartic and
incompatible-pair-product comparisons are separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRepeatedRunCostUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum

theorem uniform_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |FourthRunRemainder.remainder G L| ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨N3, _hN3, htriple⟩ := HalfPowerThirdActivityUnderBCN.uniform_absolute_activity c κ hc hBCN C η hη
  obtain ⟨N2, _hN2, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NP, hcap⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (72 * K + 72 * K ^ 2 + 6 * K ^ 4)
    (-3 / 2 + η) η hη
  refine ⟨max NM (max N3 (max N2 (max NP NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp (x : ℕ) (hx : x ∈ G) : infiniteMarginal x L ≤ K / N := by
    calc
      _ ≤ 2 * (2 ^ L : ℝ)⁻¹ := hcap N (by omega) L hband x (hG hx)
      _ ≤ 2 * ((2 : ℝ) ^ C / N) :=
        mul_le_mul_of_nonneg_left (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) (by norm_num)
      _ = _ := by dsimp [K]; ring
  have hm : actualMean G L ≤ K := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  have hfirst : 72 * (K / N) * (N : ℝ) ^ (-1 / 2 + η) = 72 * K * (N : ℝ) ^ (-3 / 2 + η) := by
    rw [show -3 / 2 + η = (-1 / 2 + η) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
    ring
  have hsecond : 72 * (K / N) ^ 2 * (N : ℝ) ^ (-1 / 2 + η) ≤
      72 * K ^ 2 * (N : ℝ) ^ (-3 / 2 + η) := by
    calc
      _ = 72 * K ^ 2 * (N : ℝ) ^ (-5 / 2 + η) := by
        rw [show -5 / 2 + η = (-1 / 2 + η) - 2 by ring, Real.rpow_sub hn, Real.rpow_two, div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity)
  have hthird : 6 * (K / N) ^ 3 * actualMean G L ≤ 6 * K ^ 4 * (N : ℝ) ^ (-3 / 2 + η) := by
    calc
      _ ≤ 6 * (K / N) ^ 3 * K := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 6 * K ^ 4 * (N : ℝ) ^ (-3 : ℝ) := by
        rw [Real.rpow_neg hn.le, Real.rpow_ofNat (N : ℝ) 3, div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hη])) (by positivity)
  have hf := FourthRunRemainder.finite_bound hG (K / N) (by positivity) hp
  calc
    _ ≤ 72 * (K / N) * (N : ℝ) ^ (-1 / 2 + η) +
        72 * (K / N) ^ 2 * (N : ℝ) ^ (-1 / 2 + η) + 6 * (K / N) ^ 3 * actualMean G L :=
      hf.trans (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (htriple N (by omega) L hband G hG) (by positivity))
        (mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity))) le_rfl)
    _ ≤ (72 * K + 72 * K ^ 2 + 6 * K ^ 4) * (N : ℝ) ^ (-3 / 2 + η) := by
      rw [hfirst]
      nlinarith only [hsecond, hthird]
    _ ≤ (N : ℝ) ^ ((-3 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.FourthRepeatedRunCostUnderBCN
