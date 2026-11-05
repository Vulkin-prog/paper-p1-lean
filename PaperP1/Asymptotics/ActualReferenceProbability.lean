module

public import PaperP1.Asymptotics.SecondCumulant
public import PaperP1.Asymptotics.ActualReferenceAdmissibility

/-! # Unconditional eventual probability status of the actual references

Both references retain the original mean and full second factorial cumulant.
No approximation rate for the original law is assumed or asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualReferenceProbability

open MeasureTheory PaperP1.Model PaperP1.CountObservables

theorem hermite_parameters (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ∧
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L <
          countMoment (dyadicBlock N) L 1 := by
  obtain ⟨NP, hNP, hpositive⟩ := PositiveSecondCumulant.uniform_positive C
  obtain ⟨NG, hNG, hgap⟩ := SecondCumulant.uniform_parameter_gap C
  exact ⟨max NP NG, by omega, fun N hN L hband ↦
    ⟨hpositive N (by omega) L hband, (hgap N (by omega) L hband).2⟩⟩

theorem uniform_quadratic_probability (C : ℝ) :
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
  obtain ⟨NS, hNS, hsmall⟩ := SecondCumulant.uniform_eventually_small C
    (m ^ 2 / (M + 1)) hδ
  obtain ⟨NP, hNP, hpositive⟩ := PositiveSecondCumulant.uniform_positive C
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max NS (max NP NM), by omega, ?_⟩
  intro N hN L hband
  have hα := hpositive N (by omega) L hband
  have hαcap := hsmall N (by omega) L hband (dyadicBlock N) (fun _ h ↦ h)
  obtain ⟨hml, hmu⟩ := hmean N (by omega) L hband
  exact ActualReferenceAdmissibility.quadratic_of_bounds hm hM hml hmu hα.le
    ((le_abs_self _).trans hαcap)

theorem uniform_hermite_probability (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicSignedLaw.IsProbability (CompletedLaw.toSignedMeasure (HermiteReference.reference
        (countMoment (dyadicBlock N) L 1)
        (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))) := by
  obtain ⟨N₀, hN₀, hparam⟩ := hermite_parameters C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hα, hαμ⟩ := hparam N hN L hband
  refine ⟨HermiteReference.law _ _ hα.le hαμ.le, ?_⟩
  exact (HermiteReference.actual_signed_reference _ _ hα.le hαμ.le).symm

end PaperP1.ActualReferenceProbability
