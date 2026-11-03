module

public import PaperP1.Probability.PositivePositionalConvolution
public import PaperP1.Probability.AtomicSignedLaw

/-! # Positive completed positional laws are genuine probability measures -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalProbabilityMeasure

open MeasureTheory PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalTotalMass PaperP1.PositionalCoefficientExpansion PaperP1.PositivePositionalConvolution

variable {ι : Type*} [MeasurableSpace (Configuration ι)]
  [MeasurableSingletonClass (Configuration ι)]

def law (ν : Space ι) (hν : IsProbability ν) : ProbabilityMeasure (Configuration ι) :=
  ⟨Measure.sum (fun v ↦ ENNReal.ofReal (coeff v ν) • Measure.dirac v),
    (hasSum_coeff_of_totalMass_eq_one ν hν.2).isProbabilityMeasure_sum_dirac hν.1⟩

theorem real_singleton (ν : Space ι) (hν : IsProbability ν) (v : Configuration ι) :
    (law ν hν : Measure (Configuration ι)).real {v} = coeff v ν := by
  change ((Measure.sum (fun w ↦ ENNReal.ofReal (coeff w ν) • Measure.dirac w)) {v}).toReal = coeff v ν
  rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hν.1 v)]

theorem law_eq_of_singletons [Countable (Configuration ι)] (ν : Space ι) (hν : IsProbability ν)
    (P : ProbabilityMeasure (Configuration ι))
    (hP : ∀ v, (P : Measure (Configuration ι)).real {v} = coeff v ν) : law ν hν = P := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_measureReal_singleton
  intro v
  rw [real_singleton, hP]

theorem totalVariation_eq (ν κ : Space ι) (hν : IsProbability ν) (hκ : IsProbability κ) :
    ((∑' v, |(law ν hν : Measure (Configuration ι)).real {v} -
      (law κ hκ : Measure (Configuration ι)).real {v}|) / 2) = ‖ν - κ‖ / 2 := by
  simp only [real_singleton, norm_eq_tsum_abs_coeff, map_sub]

end PaperP1.PositionalProbabilityMeasure
