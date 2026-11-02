module

public import PaperP1.Asymptotics.NonalignedActivityUnderBCN
public import PaperP1.Asymptotics.AlignedActivityPower
public import PaperP1.Asymptotics.SecondCumulantUnderBCN

/-! # A strictly improved coarse pair rate, retaining the explicit BCN premise -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RefinedPairActivityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NonalignedJointProbabilityUnderBCN
  PaperP1.HeterogeneousRunConversion PaperP1.CountObservables

theorem rankSlope_ge_third : (1 / 3 : ℝ) ≤ rankSlope := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  unfold rankSlope
  linarith only [hh]

theorem absolute_partition (N L : ℕ) :
    CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
      CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) = absoluteMass (dyadicBlock N) L := by
  classical
  exact sum_sdiff (f := fun e ↦ |infiniteCenteredCoefficient L e|) (filter_subset _ _)

theorem uniform_pair_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      absoluteMass G L ≤ (N : ℝ) ^ (-1 + rankSlope + ε) := by
  obtain ⟨NN, _hNN, hn⟩ := NonalignedActivityUnderBCN.uniform_bound c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := AlignedActivityPower.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + rankSlope + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NN (max NA NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have halign : CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) ≤
      (N : ℝ) ^ (-1 + rankSlope + ε / 2) :=
    (ha N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [rankSlope_ge_third]))
  have hnon := hn N (by omega) L hband
  have hpart := absolute_partition N L
  calc
    _ ≤ absoluteMass (dyadicBlock N) L := PairActivityHostCap.absoluteMass_mono hG L
    _ ≤ 2 * (N : ℝ) ^ (-1 + rankSlope + ε / 2) := by linarith only [hpart, halign, hnon]
    _ ≤ (N : ℝ) ^ ((-1 + rankSlope + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_cumulant (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤
        (N : ℝ) ^ (-1 + rankSlope + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := uniform_pair_activity c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨K, _hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + K ^ 2)
    (-1 + rankSlope + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NA (max NM NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ (hm N (by omega) L x hband (hG hx)).2)
  have hd : HeterogeneousBernoulli.powerSum G (fun x ↦ infiniteMarginal x L) 2 ≤
      K ^ 2 * (N : ℝ) ^ (-1 + rankSlope + ε / 2) := by
    calc
      _ ≤ K ^ 2 / N := hdiag
      _ = K ^ 2 * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
        (by linarith only [rankSlope_pos, hε])) (sq_nonneg K)
  have hfinite := PairActivityHostCap.second_cumulant_absolute_bound (L := L) hG
  have hactivity := ha N (by omega) L hband G hG
  calc
    _ ≤ (2 + K ^ 2) * (N : ℝ) ^ (-1 + rankSlope + ε / 2) := by
      linarith only [hfinite, hactivity, hd]
    _ ≤ (N : ℝ) ^ ((-1 + rankSlope + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_conversion (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
        QuadraticPoisson.reference (countMoment G L 1)
          (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
        (N : ℝ) ^ (-2 + rankSlope + ε) := by
  let K := HeterogeneousRunConversionAsymptotic.errorConstant C
  have hK : 0 < K := HeterogeneousRunConversionAsymptotic.errorConstant_pos C
  obtain ⟨NA, _hNA, ha⟩ := uniform_pair_activity c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NE, _hNE, he⟩ := HeterogeneousRunConversionAsymptotic.uniform_actual_bound C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * K)
    (-2 + rankSlope + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NA (max NE NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsquare : 1 / (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (-2 + rankSlope + ε / 2) := by
    rw [one_div, ← Real.rpow_two, ← Real.rpow_neg hn.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [rankSlope_pos, hε])
  have hpair : absoluteMass G L / N ≤ (N : ℝ) ^ (-2 + rankSlope + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 + rankSlope + ε / 2) / N :=
        div_le_div_of_nonneg_right (ha N (by omega) L hband G hG) hn.le
      _ = _ := by
        rw [show (-2 + rankSlope + ε / 2) = (-1 + rankSlope + ε / 2) - 1 by ring,
          Real.rpow_sub hn, Real.rpow_one]
  calc
    _ ≤ K * (1 / (N : ℝ) ^ 2 + absoluteMass G L / N) := he N (by omega) L hband G hG
    _ ≤ K * ((N : ℝ) ^ (-2 + rankSlope + ε / 2) + (N : ℝ) ^ (-2 + rankSlope + ε / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsquare hpair) hK.le
    _ = (2 * K) * (N : ℝ) ^ (-2 + rankSlope + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-2 + rankSlope + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RefinedPairActivityUnderBCN
