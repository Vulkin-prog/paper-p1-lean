module

public import PaperP1.Asymptotics.PositiveSecondCumulant
public import PaperP1.Probability.HermiteReference

/-! # Eventual probability status of the actual quadratic and Hermite references

All parameters are the original infinite-model mean and second factorial
cumulant. BCN remains one explicit ordinary argument for the upper bound.
Eventual positivity of the cumulant itself is proved unconditionally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualReferenceAdmissibility

open MeasureTheory PaperP1.Model PaperP1.CountObservables PaperP1.CharlierQuadratic

/-- A uniform sufficient domain, derived from the exact integer Charlier minimum. -/
theorem quadratic_of_bounds {m M μ α : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hml : m ≤ μ) (hmu : μ ≤ M) (hα : 0 ≤ α) (hcap : α ≤ m ^ 2 / (M + 1)) :
    AtomicSignedLaw.IsProbability (QuadraticPoisson.reference μ α) := by
  have hμ : 0 < μ := hm.trans_le hml
  apply (QuadraticPoisson.main_8_1 μ α hμ).mpr
  refine ⟨hα, (le_div_iff₀ (minimumMagnitude_pos μ hμ)).mpr ?_⟩
  have ht : theta μ * (1 - theta μ) ≤ 1 := by nlinarith only [sq_nonneg (theta μ - 1 / 2)]
  have hden : μ + theta μ * (1 - theta μ) ≤ M + 1 := by linarith only [hmu, ht]
  have hδ : 0 ≤ m ^ 2 / (M + 1) := by positivity
  have hprod := mul_le_mul hcap hden
    (le_of_lt (minimumMagnitude_pos μ hμ)) hδ
  have heq : (m ^ 2 / (M + 1)) * (M + 1) = m ^ 2 :=
    div_mul_cancel₀ _ (by positivity : M + 1 ≠ 0)
  rw [heq] at hprod
  have hsq := pow_le_pow_left₀ hm.le hml 2
  dsimp only [minimumMagnitude]
  nlinarith only [hprod, hsq, sq_nonneg μ]

theorem uniform_quadratic_probability (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicSignedLaw.IsProbability (QuadraticPoisson.reference
        (countMoment (dyadicBlock N) L 1)
        (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)) := by
  let m := CriticalActualMean.lowerMean C
  let M := 2 * (2 : ℝ) ^ C
  have hm : 0 < m := CriticalActualMean.lowerMean_pos C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hδ : 0 < m ^ 2 / (M + 1) := by positivity
  obtain ⟨NS, hNS, hsmall⟩ := SecondCumulantUnderBCN.uniform_eventually_small c κ hc hBCN C
    (m ^ 2 / (M + 1)) hδ
  obtain ⟨NP, hNP, hpositive⟩ := PositiveSecondCumulant.uniform_positive C
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max NS (max NP NM), by omega, ?_⟩
  intro N hN L hband
  have hα := hpositive N (by omega) L hband
  have hαcap := hsmall N (by omega) L hband (dyadicBlock N) (fun _ h ↦ h)
  obtain ⟨hml, hmu⟩ := hmean N (by omega) L hband
  exact quadratic_of_bounds hm hM hml hmu hα.le ((le_abs_self _).trans hαcap)

theorem uniform_hermite_probability (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicSignedLaw.IsProbability (CompletedLaw.toSignedMeasure (HermiteReference.reference
        (countMoment (dyadicBlock N) L 1)
        (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))) := by
  obtain ⟨N₀, hN₀, hparam⟩ := PositiveSecondCumulant.uniform_hermite_admissibility c κ hc hBCN C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hα, hαμ⟩ := hparam N hN L hband
  refine ⟨HermiteReference.law _ _ hα.le hαμ.le, ?_⟩
  exact (HermiteReference.actual_signed_reference _ _ hα.le hαμ.le).symm

end PaperP1.ActualReferenceAdmissibility
