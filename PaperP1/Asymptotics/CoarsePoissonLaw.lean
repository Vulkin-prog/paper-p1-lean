module

public import PaperP1.Asymptotics.CoarseFixedFactorialMoments
public import PaperP1.Probability.CompletedFactorialTruncation
public import PaperP1.Probability.CompletedPoissonMetric
public import PaperP1.Model.RetainedModifiedLaw
public import PaperP1.Probability.AtomicProbabilityMetric

/-! # Uniform Poisson approximation of the actual original count without unproved inputs

The reconstruction order is fixed after the final tolerance and before N.
No quantitative original-law approximation or growing-order moment estimate
is assumed. The reference retains the actual mean at every scale.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarsePoissonLaw

open Finset Filter MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability
  PaperP1.CountObservables PaperP1.FactorialCountMoments PaperP1.HeterogeneousDirectMaximum
  PaperP1.CompletedLaw PaperP1.CompletedPoisson PaperP1.FactorialCountTruncation

def actualPoissonLaw (N L : ℕ) : ProbabilityMeasure ℕ :=
  CompletedPoissonMetric.law (actualMean (dyadicBlock N) L)
    (sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem realMass_actualPoissonLaw (N L k : ℕ) :
    AtomicProbability.realMass (actualPoissonLaw N L) k =
      PoissonSequence.mass (actualMean (dyadicBlock N) L) k :=
  CompletedPoissonMetric.realMass_law _ _ k

theorem uniform_finite_orders (K : ℕ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r ∈ range (K + 1),
      |factorialCountMoment (dyadicBlock N) L r - actualMean (dyadicBlock N) L ^ r| ≤
        (N : ℝ) ^ (-1 / 4 : ℝ) := by
  have heach (r : ℕ) (_hr : r ∈ range (K + 1)) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |factorialCountMoment (dyadicBlock N) L r - actualMean (dyadicBlock N) L ^ r| ≤
        (N : ℝ) ^ (-1 / 4 : ℝ) := by
    obtain ⟨NR, _hNR, hR⟩ := CoarseFixedFactorialMoments.uniform_actual_error r C (1 / 4) (by norm_num)
    refine eventually_atTop.mpr ⟨NR, ?_⟩
    intro N hN L hband
    simpa only [show (-1 / 2 : ℝ) + 1 / 4 = -1 / 4 by ring] using hR N hN L hband
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (range (K + 1))).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband r hr
  exact hF N (by omega) r hr L hband

theorem uniform_completed_distance (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ‖ofFinite (restrictedCountLaw N L (dyadicBlock N)) - poisson (actualMean (dyadicBlock N) L)‖ ≤ ε := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let A : ℝ := 2 * (M + 1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha := (NormedSpace.expSeries_div_hasSum_exp A).summable.tendsto_atTop_zero
  have htail : Tendsto (fun k : ℕ ↦ (2 + Real.exp (2 * M)) * (A ^ k / (k.factorial : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using ha.const_mul (2 + Real.exp (2 * M))
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((tendsto_order.mp htail).2 (ε / 2) (by positivity))
  let k := max 1 R
  have hk : 1 ≤ k := le_max_left _ _
  have hsmall : (2 + Real.exp (2 * M)) * (A ^ k / (k.factorial : ℝ)) ≤ ε / 2 :=
    (hR k (le_max_right _ _)).le
  let W : ℝ := ∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ)
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NQ, _hNQ, horders⟩ := uniform_finite_orders k C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (2 * W / ε) (-1 / 4) (1 / 4) (by norm_num)
  refine ⟨max NM (max NQ NF), by omega, ?_⟩
  intro N hN L hband
  let μ := actualMean (dyadicBlock N) L
  let T := (N : ℝ) ^ (-1 / 4 : ℝ)
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : μ ≤ M := by
    dsimp only [μ]
    rw [actualMean_eq_countMoment (subset_refl _)]
    exact (hmean N (by omega) L hband).2
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT : T ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 / 4 : ℝ) ≤ 0)
  have hbudget : W * T ≤ ε / 2 := by
    have hf := hfactor N (by omega)
    norm_num only [show (-1 / 4 : ℝ) + 1 / 4 = 0 by ring, Real.rpow_zero] at hf
    have hs := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ ε / 2)
    have hid : (ε / 2) * (2 * W / ε) = W := by field_simp
    rw [← mul_assoc, hid, mul_one] at hs
    simpa only [T, neg_div] using hs
  have hfac : factorialCountMoment (dyadicBlock N) L k ≤ M ^ k + 1 := by
    have h := horders N (by omega) L hband k (mem_range.mpr (by omega))
    have hs := le_abs_self (factorialCountMoment (dyadicBlock N) L k - μ ^ k)
    have hp := pow_le_pow_left₀ hμ hμM k
    change |factorialCountMoment (dyadicBlock N) L k - μ ^ k| ≤ T at h
    linarith only [h, hs, hp, hT]
  have hmajor : M ^ k + 1 ≤ 2 * (M + 1) ^ k := by
    have hp := pow_le_pow_left₀ hM (by linarith : M ≤ M + 1) k
    have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ M + 1) k
    rw [one_pow] at h1
    linarith only [hp, h1]
  have hfirst : (2 : ℝ) ^ k / (k.factorial : ℝ) * factorialCountMoment (dyadicBlock N) L k ≤
      2 * (A ^ k / (k.factorial : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ k / (k.factorial : ℝ) * (2 * (M + 1) ^ k) :=
        mul_le_mul_of_nonneg_left (hfac.trans hmajor) (by positivity)
      _ = _ := by dsimp [A]; rw [mul_pow]; ring
  have hlast : (2 * μ) ^ k / (k.factorial : ℝ) * Real.exp (2 * μ) ≤
      (A ^ k / (k.factorial : ℝ)) * Real.exp (2 * M) := by
    apply mul_le_mul
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by dsimp [A]; linarith only [hμM]) k
    · exact Real.exp_le_exp.mpr (by linarith only [hμM])
    · exact (Real.exp_pos _).le
    · positivity
  have hpoly : (∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ) *
      |factorialCountMoment (dyadicBlock N) L r - μ ^ r|) ≤ ε / 2 := by
    calc
      _ ≤ ∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ) * T := by
        apply sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          (horders N (by omega) L hband r (mem_range.mpr (by have h := mem_range.mp hr; omega))) (by positivity)
      _ = W * T := (sum_mul _ _ _).symm
      _ ≤ _ := hbudget
  have hmom (r : ℕ) : moment (dyadicBlock N) (cylinderProbability (dyadicCutoff N L))
      (fun x ↦ startIndicator x L) r = factorialCountMoment (dyadicBlock N) L r :=
    (factorialCountMoment_eq_finite (subset_refl _) r).symm
  have hd := CompletedFactorialTruncation.count_distance_bound (dyadicBlock N)
    (cylinderProbability (dyadicCutoff N L)) (fun x ↦ startIndicator x L) μ hμ k hk
  simp only [hmom] at hd
  change ‖ofFinite (countLaw (dyadicBlock N) (cylinderProbability (dyadicCutoff N L)).weight
    (fun x ↦ startIndicator x L)) - poisson μ‖ ≤ ε
  nlinarith only [hd, hfirst, hlast, hpoly, hsmall]

theorem uniform_totalVariation (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (actualPoissonLaw N L) ≤ ε := by
  obtain ⟨N₀, hN₀, hnorm⟩ := uniform_completed_distance C (2 * ε) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hP (k : ℕ) : AtomicProbability.realMass (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) k =
      (restrictedCountLaw N L (dyadicBlock N)).coeff k := by
    rw [RetainedModifiedLaw.realMass_originalLaw, restrictedCountLaw_coeff (subset_refl _)]
  have h := CompletedPoissonMetric.totalVariation_bound (restrictedCountLaw N L (dyadicBlock N))
    (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) hP (actualMean (dyadicBlock N) L)
    (sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  exact h.trans (by have hb := hnorm N hN L hband; linarith only [hb])

def nominalPoissonLaw (N L : ℕ) : ProbabilityMeasure ℕ :=
  CompletedPoissonMetric.law (FiniteChannelHierarchy.nominalMean N L)
    (by unfold FiniteChannelHierarchy.nominalMean; positivity)

theorem uniform_nominal_totalVariation (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (nominalPoissonLaw N L) ≤ ε := by
  obtain ⟨NP, _hNP, hpois⟩ := uniform_totalVariation C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbias⟩ := CoarseFixedFactorialMoments.uniform_power_mean_bias 1 C (1 / 2) (by norm_num)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (2 / ε) (-1 / 2) (1 / 2) (by norm_num)
  refine ⟨max 2 (max NP (max NB NF)), by omega, ?_⟩
  intro N hN L hband
  have hf := hfactor N (by omega)
  norm_num only [show (-1 / 2 : ℝ) + 1 / 2 = 0 by ring, Real.rpow_zero] at hf
  have hs := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ ε / 2)
  have hid : (ε / 2) * (2 / ε) = 1 := by field_simp
  rw [← mul_assoc, hid, one_mul, mul_one] at hs
  have hb : |actualMean (dyadicBlock N) L - FiniteChannelHierarchy.nominalMean N L| ≤ ε / 2 := by
    have hp := hbias N (by omega) L hband
    norm_num only [pow_one, show (-1 : ℝ) + 1 / 2 = -1 / 2 by ring] at hp
    exact hp.trans (by simpa only [neg_div] using hs)
  have hdist : AtomicProbability.totalVariation (actualPoissonLaw N L) (nominalPoissonLaw N L) ≤ ε / 2 :=
    (CompletedPoissonMetric.parameter_stability _ _ _ _).trans hb
  have ht := AtomicProbabilityMetric.triangle (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
    (actualPoissonLaw N L) (nominalPoissonLaw N L)
  have hp := hpois N (by omega) L hband
  linarith only [ht, hp, hdist]

end PaperP1.CoarsePoissonLaw
