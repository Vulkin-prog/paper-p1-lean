module

public import PaperP1.Asymptotics.SubpowerFixedCountMoments
public import PaperP1.Asymptotics.ActualReferenceAdmissibility
public import PaperP1.Asymptotics.PolynomialWeightedSequenceRate
public import PaperP1.Model.OriginalLawPolynomialMoments
public import PaperP1.Probability.PoissonPolynomialMoments

/-! # Subpolynomial moments for the original count and its actual quadratic reference

BCN is needed only for eventual admissibility and boundedness of the reference
parameters. The original-law moment estimate is independent of BCN. Every order
is fixed before the threshold; no higher moment bound is assumed as an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualQuadraticSubpowerMoments

open Finset PaperP1.Model PaperP1.CountObservables PaperP1.PoissonSequence
  PaperP1.AtomicProbability

def original (N L k : ℕ) : ℝ := realMass (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) k

def quadratic (N L k : ℕ) : ℝ := quadraticMass (countMoment (dyadicBlock N) L 1)
  (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L) k

theorem uniform_moments (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PolynomialWeightedSequenceRate.MomentBounds (fun k : ℕ ↦ 1 + (k : ℝ))
        (original N L) (quadratic N L) r ((N : ℝ) ^ δ) := by
  let M := 2 * (2 : ℝ) ^ C
  obtain ⟨B, _hB, hq⟩ := PoissonPolynomialMoments.uniform_absolute_moment M (by dsimp [M]; positivity) r
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NS, _hNS, hs⟩ := SecondCumulantUnderBCN.uniform_eventually_small c κ hc hBCN C 1 (by norm_num)
  obtain ⟨NP, _hNP, hp⟩ := ActualReferenceAdmissibility.uniform_quadratic_probability c κ hc hBCN C
  obtain ⟨NO, _hNO, ho⟩ := SubpowerFixedCountMoments.uniform_ordinary r C (δ / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ r * 2) (δ / 2) (δ / 2) (by positivity)
  obtain ⟨NB, hb⟩ := HalfCountSchedule.factor_absorption B 0 δ hδ
  refine ⟨max 2 (max NM (max NS (max NP (max NO (max NF NB))))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hμ : 0 ≤ countMoment (dyadicBlock N) L 1 :=
    (CriticalActualMean.lowerMean_pos C).le.trans (hm N (by omega) L hband).1
  have hqn : ∀ k, 0 ≤ quadratic N L k := by
    have hh := hp N (by omega) L hband
    rw [QuadraticPoisson.reference,
      AtomicSignedLaw.isProbability_ofSequence_iff (hasSum_quadraticMass _ _ hμ)] at hh
    exact hh
  obtain ⟨hqs, hqb⟩ := hq _ _ hμ (hm N (by omega) L hband).2
    (hs N (by omega) L hband (dyadicBlock N) (subset_refl _))
  have hqabs : (fun k ↦ |quadratic N L k| * (1 + (k : ℝ)) ^ r) =
      (fun k ↦ quadratic N L k * (1 + (k : ℝ)) ^ r) := by
    funext k
    rw [abs_of_nonneg (hqn k)]
  change Summable (fun k ↦ |quadratic N L k| * (1 + (k : ℝ)) ^ r) at hqs
  change (∑' k, |quadratic N L k| * (1 + (k : ℝ)) ^ r) ≤ B at hqb
  rw [hqabs] at hqs hqb
  obtain ⟨hos, hob⟩ := OriginalLawPolynomialMoments.weighted_moment_bound (dyadicBlock N) L r
  refine ⟨fun k ↦ realMass_nonneg _ k, hqn, hos, hqs, ?_, ?_⟩
  · have hlarge : 1 ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hn1 (by positivity)
    have hmoment := ho N (by omega) L hband (dyadicBlock N) (subset_refl _)
    calc
      _ ≤ (2 : ℝ) ^ r * (1 + countMoment (dyadicBlock N) L r) := hob
      _ ≤ ((2 : ℝ) ^ r * 2) * (N : ℝ) ^ (δ / 2) := by
        have hmul := mul_le_mul_of_nonneg_left (add_le_add hlarge hmoment) (by positivity : (0 : ℝ) ≤ 2 ^ r)
        nlinarith only [hmul]
      _ ≤ (N : ℝ) ^ (δ / 2 + δ / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  · have hB : B ≤ (N : ℝ) ^ δ := by
      simpa only [Real.rpow_zero, mul_one, zero_add] using hb N (by omega)
    exact hqb.trans hB

end PaperP1.ActualQuadraticSubpowerMoments
