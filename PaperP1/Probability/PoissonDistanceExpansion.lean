module

public import PaperP1.Probability.QuadraticReferenceDistance
public import PaperP1.Probability.PoissonParameterStability
public import PaperP1.Probability.SignedAtomicDistance

/-! # Exact Poisson distance expansion from an actual quadratic approximation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonDistanceExpansion

open MeasureTheory

theorem zero_reference (μ : ℝ) (hμ : 0 ≤ μ) :
    QuadraticPoisson.reference μ 0 = (QuadraticPoisson.poissonLaw μ hμ : Measure ℕ).toSignedMeasure := by
  rw [QuadraticPoisson.reference_eq_poisson_plus_secondDifference μ 0 hμ]
  simp only [zero_div, zero_smul, add_zero]
  exact QuadraticPoisson.poissonSigned_eq_poissonMeasure μ hμ

theorem distance_symm (P Q : SignedMeasure ℕ) :
    SignedAtomicDistance.distance P Q = SignedAtomicDistance.distance Q P := by
  unfold SignedAtomicDistance.distance
  exact tsum_congr fun _ ↦ abs_sub_comm _ _

theorem finite_expansion (P : ProbabilityMeasure ℕ) (μ α : ℝ) (hμ : 0 ≤ μ) (hα : 0 ≤ α) :
    |AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw μ hμ) -
      α / 4 * PoissonDifferenceSigned.norm μ 2| ≤
      SignedAtomicDistance.distance (P : Measure ℕ).toSignedMeasure (QuadraticPoisson.reference μ α) / 2 := by
  let Q := QuadraticPoisson.reference μ α
  let S := (QuadraticPoisson.poissonLaw μ hμ : Measure ℕ).toSignedMeasure
  let R := (P : Measure ℕ).toSignedMeasure
  have hgap : SignedAtomicDistance.distance Q S = α / 2 * PoissonDifferenceSigned.norm μ 2 := by
    have hh := QuadraticReferenceDistance.signed_distance μ α 0 hμ
    rw [zero_reference μ hμ] at hh
    simpa only [SignedAtomicDistance.distance, _root_.sub_apply, sub_zero, abs_of_nonneg hα] using hh
  have h1 := SignedAtomicDistance.triangle R Q S
  have h2 := SignedAtomicDistance.triangle Q R S
  rw [distance_symm Q R] at h2
  have hd : SignedAtomicDistance.distance R S = 2 * AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw μ hμ) :=
    SignedAtomicDistance.probability_eq _ _
  rw [hd, hgap] at h1 h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

theorem finite_mean_change (P : ProbabilityMeasure ℕ) (μ ν : ℝ) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) :
    |AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw μ hμ) -
      AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw ν hν)| ≤ |μ - ν| := by
  let S := (QuadraticPoisson.poissonLaw μ hμ : Measure ℕ).toSignedMeasure
  let T := (QuadraticPoisson.poissonLaw ν hν : Measure ℕ).toSignedMeasure
  let R := (P : Measure ℕ).toSignedMeasure
  have hs : SignedAtomicDistance.distance S T ≤ 2 * |μ - ν| := by
    have hh := PoissonParameterStability.actual_signed_difference hμ hν 0 0
    rw [zero_reference μ hμ, zero_reference ν hν] at hh
    simpa only [SignedAtomicDistance.distance, _root_.sub_apply, abs_zero, mul_zero,
      mul_one, sub_self, add_zero] using hh
  have h1 := SignedAtomicDistance.triangle R S T
  have h2 := SignedAtomicDistance.triangle R T S
  rw [distance_symm T S] at h2
  have hdS : SignedAtomicDistance.distance R S = 2 * AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw μ hμ) :=
    SignedAtomicDistance.probability_eq _ _
  have hdT : SignedAtomicDistance.distance R T = 2 * AtomicProbability.totalVariation P (QuadraticPoisson.poissonLaw ν hν) :=
    SignedAtomicDistance.probability_eq _ _
  rw [hdS, hdT] at h1 h2
  exact abs_le.mpr ⟨by linarith only [h1, hs], by linarith only [h2, hs]⟩

end PaperP1.PoissonDistanceExpansion
