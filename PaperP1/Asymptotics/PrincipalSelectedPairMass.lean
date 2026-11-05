module

public import PaperP1.Asymptotics.SelectedPairCriticalMass
public import PaperP1.Analysis.SelectedPairWeightedSeries
public import PaperP1.Asymptotics.PairProfiles
public import PaperP1.Asymptotics.SecondFactorialCorrectionLower

/-! # The selected good-pair family at every critical order, with actual mean and cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalSelectedPairMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.CriticalFreshBranchingBudget PaperP1.CriticalBandScale

def selected (N H L r : ℕ) : ℝ :=
  SelectedPairBranchingTuples.mass (dyadicBlock N) (PrincipalChannelEdges.edges N H L) N L (r - 2)

def amplitude (N H L : ℕ) : ℝ := SelectedPairCriticalMass.amplitude (PrincipalChannelEdges.edges N H L) L

def mean (N L : ℕ) : ℝ := countMoment (dyadicBlock N) L 1

def alpha (N L : ℕ) : ℝ := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L

def weightedError (N H L m : ℕ) : ℝ :=
  SelectedPairWeightedSeries.error (selected N H L) (mean N L) (alpha N L) m

theorem amplitude_eq_beta (N H L : ℕ) : amplitude N H L = 2 * PrincipalChannelEdges.beta N H L := rfl

theorem source_dependent {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    ∀ e ∈ PrincipalChannelEdges.edges N H L, 0 < runRelativeNullity L e := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact PrivateChannelRank.nullity_positive hN (by decide : 0 < 2) (by decide : 2 < 3)
      (by omega) (mem_filter.mp he).1
  · exact PrivateChannelRank.nullity_positive hN (by decide : 0 < 3) (by decide : 3 < 4)
      (by omega) (mem_filter.mp he).1

theorem uniform_first (K C : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, 2 ≤ m → (m : ℝ) ≤ orderCap K N →
      ∀ L H : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ r : ℕ, 2 ≤ r → r ≤ m →
        |selected N H L r - (r.choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ (r - 2) * amplitude N H L| ≤
        ((r.choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ (r - 2) * amplitude N H L) *
          (((r - 2 : ℕ) : ℝ) * freshEnvelope K N / N) := by
  obtain ⟨NB, _hNB, hb⟩ := SelectedPairCriticalMass.uniform_bound K C hK
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 3 (max NB NG), by omega, ?_⟩
  intro N hN m hm horder L H hband r hr hrm
  have hlarge := (hg N (by omega) L hband).2
  have hh := hb N (by omega) m hm horder L hband (PrincipalChannelEdges.edges N H L)
    (PrincipalChannelEdges.subset_pairs (by omega) hlarge) (source_dependent (by omega) hlarge)
    (r - 2) (by omega)
  simpa only [selected, amplitude, Nat.sub_add_cancel hr] using hh

theorem amplitude_upper (C : ℝ) (D : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      amplitude N H L ≤ (N : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨_c, K, _hc, hK, NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨NW, hw⟩ := critical_band_scale C
  obtain ⟨NF, hf⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    (2 * K) 1 (1 / 6) (by norm_num)
  refine ⟨max 3 (max NP (max NW NF)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : 2 * K * (L + 1 : ℝ) ≤ (N : ℝ) ^ (1 / 6 : ℝ) := by
    simpa only [pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * K * (L + 1 : ℝ))] using
      hf N (by omega) L (hw N (by omega) L hband).2
  calc
    _ ≤ 2 * (K * L * (N : ℝ) ^ (-2 / 3 : ℝ)) := by
      rw [amplitude_eq_beta]
      exact mul_le_mul_of_nonneg_left (hp N (by omega) L H hband hcut hH).2 (by norm_num)
    _ ≤ (2 * K * (L + 1 : ℝ)) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right (show (L : ℝ) ≤ L + 1 by linarith)
        (by positivity : (0 : ℝ) ≤ 2 * K * (N : ℝ) ^ (-2 / 3 : ℝ))
      convert hh using 1 <;> ring
    _ ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; norm_num

theorem uniform_weighted (C : ℝ) (D : ℕ) :
    ∀ K : ℝ, 0 ≤ K → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ,
      2 ≤ m → (m : ℝ) ≤ orderCap K N → ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        weightedError N H L m ≤ (N : ℝ) ^ (-3 / 4 : ℝ) := by
  obtain ⟨NP, _hNP, hp⟩ := PairProfiles.uniform_profiles C (1 / 40) D (by norm_num)
  obtain ⟨NA, _hNA, ha⟩ := amplitude_upper C D
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NB, _hNB, hb⟩ := CriticalActualMean.uniform_nominal_bias C (1 / 40) (by norm_num)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  let M := max 1 (2 * (2 : ℝ) ^ C)
  let T := 6 * Real.exp (Real.exp 1 * (2 * M))
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (T * (2 + (2 : ℝ) ^ C)) (-31 / 40) (1 / 40) (by norm_num)
  intro K hK
  obtain ⟨NS, _hNS, hs⟩ := SelectedPairCriticalMass.uniform_numeric_bound K C (1 / 24) hK (by norm_num)
  refine ⟨10 + NA + NM + NB + NG + NF + NP + NS, by omega, ?_⟩
  intro N hN m hmorder horder L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let ellMean := (N : ℝ) * (2 ^ L : ℝ)⁻¹
  let A := amplitude N H L
  let δ := (N : ℝ) ^ (-7 / 24 : ℝ)
  have hA : 0 ≤ A := SelectedPairCriticalMass.amplitude_nonneg _ _
  have hAcap : A ≤ (N : ℝ) ^ (-1 / 2 : ℝ) := ha N (by omega) L H hband hcut hH
  have hA1 : A ≤ 1 := hAcap.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num))
  have hMean := hm N (by omega) L hband
  have hμ : 0 ≤ mean N L := (CriticalActualMean.lowerMean_pos C).le.trans hMean.1
  have hμM : mean N L ≤ M := hMean.2.trans (le_max_right _ _)
  have hE : 0 ≤ ellMean := by dsimp [ellMean]; positivity
  have hEM : ellMean ≤ M := by
    have hh := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband
    have hEll : ellMean ≤ (2 : ℝ) ^ C := by
      dsimp [ellMean]
      have hb := (le_div_iff₀ hn).mp hh
      simpa only [mul_comm] using hb
    have htwo : (2 : ℝ) ^ C ≤ 2 * (2 : ℝ) ^ C := by
      have hp : 0 ≤ (2 : ℝ) ^ C := by positivity
      linarith only [hp]
    exact hEll.trans (htwo.trans (le_max_right _ _))
  have hM : 1 ≤ M := le_max_left _ _
  have hδ : 0 ≤ δ := Real.rpow_nonneg hn.le _
  have hB : ∀ r ∈ Icc 2 m,
      |selected N H L r - (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A| ≤
        (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A * δ := by
    intro r hr
    obtain ⟨hr2, hrm⟩ := mem_Icc.mp hr
    have hh := hs N (by omega) m hmorder horder L hband (PrincipalChannelEdges.edges N H L)
      (PrincipalChannelEdges.subset_pairs (by omega) (hg N (by omega) L hband).2)
      (source_dependent (by omega) (hg N (by omega) L hband).2) (r - 2) (by omega)
    simpa only [selected, amplitude, ellMean, A, δ, Nat.sub_add_cancel hr2, show (-1 / 3 : ℝ) + 1 / 24 = -7 / 24 by norm_num] using hh
  have hseries := SelectedPairWeightedSeries.finite_bound (selected N H L) ellMean (mean N L) A (alpha N L) M δ m
    hE hμ hA hM hEM hμM hδ hB
  have hPair : |A - alpha N L| ≤ (N : ℝ) ^ (-31 / 40 : ℝ) := by
    have hh := (hp N (by omega) L H hband hcut hH).1
    simpa only [A, amplitude_eq_beta, alpha, abs_sub_comm, show (-4 / 5 : ℝ) + 1 / 40 = -31 / 40 by norm_num] using hh
  have hMeanGap : |ellMean - mean N L| ≤ (2 : ℝ) ^ C * (N : ℝ) ^ (-39 / 40 : ℝ) := by
    have hh := hb N (by omega) L hband
    simpa only [ellMean, mean, abs_sub_comm, show (-1 : ℝ) + 1 / 40 = -39 / 40 by norm_num] using hh
  have hAδ : A * δ ≤ (N : ℝ) ^ (-31 / 40 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 / 2 : ℝ) * (N : ℝ) ^ (-7 / 24 : ℝ) := mul_le_mul_of_nonneg_right hAcap hδ
      _ = (N : ℝ) ^ (-19 / 24 : ℝ) := by rw [← Real.rpow_add hn]; congr 1; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hAμ : A * |ellMean - mean N L| ≤ (2 : ℝ) ^ C * (N : ℝ) ^ (-31 / 40 : ℝ) := by
    calc
      _ ≤ 1 * ((2 : ℝ) ^ C * (N : ℝ) ^ (-39 / 40 : ℝ)) := mul_le_mul hA1 hMeanGap (abs_nonneg _) (by norm_num)
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (by positivity)
  have hcost : A * δ + A * |ellMean - mean N L| + |A - alpha N L| ≤
      (2 + (2 : ℝ) ^ C) * (N : ℝ) ^ (-31 / 40 : ℝ) := by linarith only [hAδ, hAμ, hPair]
  calc
    _ ≤ T * (A * δ + A * |ellMean - mean N L| + |A - alpha N L|) := hseries
    _ ≤ T * ((2 + (2 : ℝ) ^ C) * (N : ℝ) ^ (-31 / 40 : ℝ)) := mul_le_mul_of_nonneg_left hcost (by dsimp [T]; positivity)
    _ = (T * (2 + (2 : ℝ) ^ C)) * (N : ℝ) ^ (-31 / 40 : ℝ) := (mul_assoc _ _ _).symm
    _ ≤ _ := by simpa only [show (-31 / 40 : ℝ) + 1 / 40 = -3 / 4 by norm_num] using hf N (by omega)

end PaperP1.PrincipalSelectedPairMass
