module

public import PaperP1.Asymptotics.SharpPairActivityUnderInputs
public import PaperP1.Asymptotics.HeterogeneousRunConversion
public import PaperP1.Asymptotics.SecondCumulantUnderBCN

/-! # The literal sharp heterogeneous conversion rate under the recorded geometric inputs

The finite signed-measure bound is unconditional. The geometric arguments
are used solely to discharge the original model's absolute pair activity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpRunConversionUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousRunConversion
  PaperP1.CountObservables

theorem uniform_cumulant (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤
        (N : ℝ) ^ (-2 / 3 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hactivity⟩ := SharpPairActivityUnderInputs.uniform_pair_activity C (ε / 2) (by positivity)
  obtain ⟨K, _hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + K ^ 2)
    (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NA, _hNA, ha⟩ := hactivity hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NA (max NM NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ (hm N (by omega) L x hband (hG hx)).2)
  have hd : HeterogeneousBernoulli.powerSum G (fun x ↦ infiniteMarginal x L) 2 ≤
      K ^ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) := by
    calc
      _ ≤ K ^ 2 / N := hdiag
      _ = K ^ 2 * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
        (by linarith only [hε])) (sq_nonneg K)
  have hfinite := PairActivityHostCap.second_cumulant_absolute_bound (L := L) hG
  have hactivity := ha N (by omega) L hband G hG
  calc
    _ ≤ (2 + K ^ 2) * (N : ℝ) ^ (-2 / 3 + ε / 2) := by
      linarith only [hfinite, hactivity, hd]
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_conversion (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
        QuadraticPoisson.reference (countMoment G L 1)
          (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
        (N : ℝ) ^ (-5 / 3 + ε)) := by
  let K := HeterogeneousRunConversionAsymptotic.errorConstant C
  have hK : 0 < K := HeterogeneousRunConversionAsymptotic.errorConstant_pos C
  obtain ⟨Ds, k, k₁, k₂, hDs, hactivity⟩ := SharpPairActivityUnderInputs.uniform_pair_activity C (ε / 2) (by positivity)
  obtain ⟨NE, _hNE, he⟩ := HeterogeneousRunConversionAsymptotic.uniform_actual_bound C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * K)
    (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NA, _hNA, ha⟩ := hactivity hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NA (max NE NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsquare : 1 / (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    rw [one_div, ← Real.rpow_two, ← Real.rpow_neg hn.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  have hpair : absoluteMass G L / N ≤ (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) / N :=
        div_le_div_of_nonneg_right (ha N (by omega) L hband G hG) hn.le
      _ = _ := by
        rw [show (-5 / 3 + ε / 2) = (-2 / 3 + ε / 2) - 1 by ring,
          Real.rpow_sub hn, Real.rpow_one]
  calc
    _ ≤ K * (1 / (N : ℝ) ^ 2 + absoluteMass G L / N) := he N (by omega) L hband G hG
    _ ≤ K * ((N : ℝ) ^ (-5 / 3 + ε / 2) + (N : ℝ) ^ (-5 / 3 + ε / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsquare hpair) hK.le
    _ = (2 * K) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring


end PaperP1.SharpRunConversionUnderInputs
