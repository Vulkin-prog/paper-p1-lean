module

public import PaperP1.Asymptotics.CoarseTripleActivityUnderBCN
public import PaperP1.Asymptotics.RepeatedRunCost

/-! # Vanishing actual third factorial cumulant with every repeated-index term

All estimates concern the original heterogeneous model. The explicit BCN
argument is the existing curve-count input, not a cumulant estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseThirdCumulantUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NonalignedJointProbabilityUnderBCN PaperP1.ThirdRunFactorialCumulant

theorem uniform_repeated_cost (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
        (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK, NR, hrepeat⟩ := RepeatedRunCost.uniform_bound C
  obtain ⟨NP, hNP, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (12 * K + 2 * K ^ 3) (-3 / 2 + η) η hη
  refine ⟨max NP (max NR NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hid : 12 * K / N * (N : ℝ) ^ (-1 / 2 + η) =
      12 * K * (N : ℝ) ^ (-3 / 2 + η) := by
    rw [show -3 / 2 + η = (-1 / 2 + η) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
    ring
  have htwo : 2 * K ^ 3 / (N : ℝ) ^ 2 ≤ 2 * K ^ 3 * (N : ℝ) ^ (-3 / 2 + η) := by
    have hi : 2 * K ^ 3 / (N : ℝ) ^ 2 = 2 * K ^ 3 * (N : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hn.le, Real.rpow_two, div_eq_mul_inv]
    rw [hi]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hη])) (by positivity)
  calc
    _ ≤ 12 * K / N * CompatibleActivitySplit.absolute L (G.powersetCard 2) +
        2 * K ^ 3 / (N : ℝ) ^ 2 := hrepeat N (by omega) L G hband hG
    _ ≤ 12 * K / N * (N : ℝ) ^ (-1 / 2 + η) + 2 * K ^ 3 / (N : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity)) le_rfl
    _ ≤ (12 * K + 2 * K ^ 3) * (N : ℝ) ^ (-3 / 2 + η) := by rw [hid]; nlinarith only [htwo]
    _ ≤ (N : ℝ) ^ ((-3 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |thirdFactorialCumulant G L| ≤ (N : ℝ) ^ (-tripleGap + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NT, hNT, htriple⟩ := CoarseTripleActivityUnderBCN.uniform_absolute_activity c κ hc hBCN C η hη
  obtain ⟨NR, hNR, hrepeat⟩ := uniform_repeated_cost c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 7 (-tripleGap + η) η hη
  refine ⟨max NT (max NR NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have htr := htriple N (by omega) L hband G hG
  have hr : |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      (N : ℝ) ^ (-tripleGap + η) :=
    (hrepeat N (by omega) L hband G hG).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [tripleGap_lt_half]))
  have hs : |CompatibleActivitySplit.signed L (G.powersetCard 3)| ≤
      CompatibleActivitySplit.absolute L (G.powersetCard 3) := abs_sum_le_sum_abs _ _
  rw [ThirdRunActivityComparison.exact_decomposition hG]
  calc
    _ ≤ |6 * CompatibleActivitySplit.signed L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| :=
      abs_add_le _ _
    _ = 6 * |CompatibleActivitySplit.signed L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := by
      rw [abs_mul]; norm_num
    _ ≤ 7 * (N : ℝ) ^ (-tripleGap + η) := by linarith only [hs, htr, hr]
    _ ≤ (N : ℝ) ^ ((-tripleGap + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_vanishing_cumulant (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |thirdFactorialCumulant G L| ≤ (N : ℝ) ^ (-tripleGap / 2) := by
  have hgap := tripleGap_pos
  simpa only [show -tripleGap + tripleGap / 2 = -tripleGap / 2 by ring] using
    uniform_bound c κ hc hBCN C (tripleGap / 2) (by positivity)

end PaperP1.CoarseThirdCumulantUnderBCN
