module

public import PaperP1.Model.DirectPairCostBound
public import PaperP1.Asymptotics.ConnectedFourthReductionUnderBCN

/-! # A proved N^(-1+epsilon) connected-fourth-cumulant comparison

This is weaker than the source N^(-3/2+epsilon) comparison. The full
source-scale reduction remains available separately with a literal
non-direct pair cost.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedFourthUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DirectPairProductComparison
  PaperP1.FourthRunFactorialCumulant

theorem uniform_nonDirect_cost (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      nonDirectApartCost G L ≤ (N : ℝ) ^ (-1 + ε) := by
  let η := ε / 2
  obtain ⟨NA, hNA, ha⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η (by dsimp [η]; positivity)
  refine ⟨NA, hNA, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let A := CompatibleActivitySplit.absolute L (G.powersetCard 2)
  let T := (N : ℝ) ^ (-1 / 2 + η)
  have hA : A ≤ T := ha N hN L hband G hG
  have hA0 : 0 ≤ A := sum_nonneg fun e _ ↦ abs_nonneg (infiniteCenteredCoefficient L e)
  have hT0 : 0 ≤ T := Real.rpow_nonneg hn.le _
  have hsq : A ^ 2 ≤ T ^ 2 := by simpa only [pow_two] using mul_le_mul hA hA hA0 hT0
  calc
    _ ≤ A ^ 2 / 2 := DirectPairCostBound.finite_bound G L
    _ ≤ T ^ 2 / 2 := div_le_div_of_nonneg_right hsq (by norm_num)
    _ ≤ T * T := by nlinarith only [sq_nonneg T]
    _ = _ := by
      dsimp [T]
      rw [← Real.rpow_add hn]
      congr 1
      dsimp [η]
      ring

theorem uniform_cumulant_comparison (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |fourthFactorialCumulant G L -
        24 * CompatibleActivitySplit.signed L (ConnectedWindowFamilies.connectedFamilies G L 4)| ≤
        (N : ℝ) ^ (-1 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NB, _hNB, hb⟩ := uniform_nonDirect_cost c κ hc hBCN C η hη
  obtain ⟨NR, _hNR, hr⟩ := ConnectedFourthReductionUnderBCN.uniform_reduction c κ hc hBCN C η hη
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 25 (-1 + η) η hη
  refine ⟨max 2 (max NB (max NR NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcost := hb N (by omega) L hband G hG
  have hreduce := hr N (by omega) L hband G hG
  have he : (N : ℝ) ^ (-3 / 2 + η) ≤ (N : ℝ) ^ (-1 + η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hfactor : 25 * (N : ℝ) ^ (-1 + η) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp [η]
    ring
  linarith only [hcost, hreduce, he, hfactor]

end PaperP1.CoarseConnectedFourthUnderBCN
