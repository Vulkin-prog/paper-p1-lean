module

public import PaperP1.Asymptotics.CoarseFixedFactorialMomentsUnderBCN
public import PaperP1.Asymptotics.CoarseIncompatibleTripleUnderBCN
public import PaperP1.Model.PositiveJointRestriction

/-! # Half-power bounds for the actual full triple activity and third cumulant

Fixed factorial moments improve the earlier small-gap estimate. The proof
keeps all repeated-index terms and all incompatible/zero-marginal families.
The sharper source exponents are not asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfPowerThirdActivityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.ThirdRunFactorialCumulant PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum
  PaperP1.PositiveMarginalRestriction PaperP1.TripleActivityConnected

theorem uniform_full_cumulant (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |thirdFactorialCumulant (dyadicBlock N) L| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨N2, _hN2, h2⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_actual_error 2 c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨N3, _hN3, h3⟩ := CoarseFixedFactorialMomentsUnderBCN.uniform_actual_error 3 c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (1 + 3 * M) (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NM (max N2 (max N3 NF)), by omega, ?_⟩
  intro N hN L hband
  let μ := actualMean (dyadicBlock N) L
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hm : μ ≤ M := by
    dsimp only [μ]
    rw [actualMean_eq_countMoment (subset_refl _)]
    exact (hmean N (by omega) L hband).2
  have hid : thirdFactorialCumulant (dyadicBlock N) L =
      (factorialCountMoment (dyadicBlock N) L 3 - μ ^ 3) -
        3 * μ * (factorialCountMoment (dyadicBlock N) L 2 - μ ^ 2) := by
    rw [thirdFactorialCumulant, factorialCountMoment_one,
      ← actualMean_eq_countMoment (subset_refl _)]
    dsimp [μ]
    ring
  rw [hid]
  calc
    _ ≤ |factorialCountMoment (dyadicBlock N) L 3 - μ ^ 3| +
        |3 * μ * (factorialCountMoment (dyadicBlock N) L 2 - μ ^ 2)| := abs_sub _ _
    _ = |factorialCountMoment (dyadicBlock N) L 3 - μ ^ 3| +
        3 * μ * |factorialCountMoment (dyadicBlock N) L 2 - μ ^ 2| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
    _ ≤ (1 + 3 * M) * (N : ℝ) ^ (-1 / 2 + ε / 2) := by
      have he2 := h2 N (by omega) L hband
      have he3 := h3 N (by omega) L hband
      have hp := mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ 3 * μ)
      have hmp := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Nat.cast_nonneg N) (-1 / 2 + ε / 2))
      linarith only [he3, hp, hmp]
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_absolute_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NK, _hNK, hcumulant⟩ := uniform_full_cumulant c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hcompare⟩ := CoarseIncompatibleTripleUnderBCN.uniform_cumulant_comparison c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, habsolute⟩ := CoarseIncompatibleTripleUnderBCN.uniform_activity_comparison c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NK (max NC (max NA NF))), by omega, ?_⟩
  intro N hN L hband G hG
  let P := positiveGround (dyadicBlock N) L
  have hP : P ⊆ dyadicBlock N := positiveGround_subset _ _
  have hp : ∀ x ∈ P, 0 < infiniteMarginal x L := fun _ hx ↦ marginal_positive hx
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let T := (N : ℝ) ^ (-1 / 2 + ε / 2)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcP : |thirdFactorialCumulant P L| ≤ T := by
    rw [← PositiveJointRestriction.third_restrict (subset_refl (dyadicBlock N))]
    exact hcumulant N (by omega) L hband
  have he : (N : ℝ) ^ (-1 + ε / 2) ≤ T :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hcmp := (hcompare N (by omega) L hband P hP hp).trans he
  have habs := (habsolute N (by omega) L hband P hP hp).2.trans he
  have hkp := (abs_le.mp hcmp).1
  have hcpos := le_abs_self (thirdFactorialCumulant P L)
  have hfull : CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) ≤ 2 * T := by
    rw [show CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) =
        CompatibleActivitySplit.absolute L (P.powersetCard 3) from
      PositiveMarginalRestriction.sum_restrict (dyadicBlock N) L 3 abs (by simp)]
    linarith only [hkp, hcpos, hcP, habs, hT]
  have hsub : G.powersetCard 3 ⊆ (dyadicBlock N).powersetCard 3 := by
    intro I hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hI
    exact mem_powersetCard.mpr ⟨hIG.trans hG, hcard⟩
  calc
    _ ≤ CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))
    _ ≤ 2 * T := hfull
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_cumulant (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |thirdFactorialCumulant G L| ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NA, _hNA, hactivity⟩ := uniform_absolute_activity c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NR, _hNR, hrepeat⟩ := CoarseThirdCumulantUnderBCN.uniform_repeated_cost c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 7 (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NA (max NR NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ha := hactivity N (by omega) L hband G hG
  have hr : |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      (N : ℝ) ^ (-1 / 2 + ε / 2) :=
    (hrepeat N (by omega) L hband G hG).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hs : |CompatibleActivitySplit.signed L (G.powersetCard 3)| ≤ CompatibleActivitySplit.absolute L (G.powersetCard 3) :=
    abs_sum_le_sum_abs _ _
  rw [ThirdRunActivityComparison.exact_decomposition hG]
  calc
    _ ≤ |6 * CompatibleActivitySplit.signed L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := abs_add_le _ _
    _ ≤ 7 * (N : ℝ) ^ (-1 / 2 + ε / 2) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      linarith only [hs, ha, hr]
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.HalfPowerThirdActivityUnderBCN
