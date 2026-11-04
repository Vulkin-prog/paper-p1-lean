module

public import PaperP1.Probability.PoissonReferenceSeparation
public import PaperP1.Probability.PoissonParameterStability
public import PaperP1.Probability.SignedAtomicDistance

/-! # Transferring two-sided mean separation from quadratic references to an actual law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticMeanLawComparison

open MeasureTheory

theorem finite_bounds (P : SignedMeasure ℕ) (μ ν M α : ℝ)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hμM : μ ≤ M) (hνM : ν ≤ M) (hα : |α| ≤ 1)
    (herror : SignedAtomicDistance.distance P (QuadraticPoisson.reference μ α) ≤
      (Real.exp (-M) / 4) * |μ - ν|) :
    (Real.exp (-M) / 4) * |μ - ν| ≤ SignedAtomicDistance.distance P (QuadraticPoisson.reference ν α) ∧
      SignedAtomicDistance.distance P (QuadraticPoisson.reference ν α) ≤
        (6 + Real.exp (-M) / 4) * |μ - ν| := by
  have hlo := PoissonReferenceSeparation.actual_reference_separation hμ hν hμM hνM (abs_le.mp hα).1
  have hhi := PoissonParameterStability.actual_signed_difference hμ hν α α
  simp only [sub_self, abs_zero, mul_zero, add_zero] at hhi
  have hid : (∑' k : ℕ, |(QuadraticPoisson.reference μ α - QuadraticPoisson.reference ν α) {k}|) =
      SignedAtomicDistance.distance (QuadraticPoisson.reference μ α) (QuadraticPoisson.reference ν α) := by
    unfold SignedAtomicDistance.distance
    simp only [_root_.sub_apply]
  rw [hid] at hlo hhi
  have hup : SignedAtomicDistance.distance (QuadraticPoisson.reference μ α) (QuadraticPoisson.reference ν α) ≤
      6 * |μ - ν| := by
    have hh := mul_le_mul_of_nonneg_right hα (abs_nonneg (μ - ν))
    nlinarith only [hhi, hh]
  have ht := SignedAtomicDistance.triangle P (QuadraticPoisson.reference μ α) (QuadraticPoisson.reference ν α)
  have hr := SignedAtomicDistance.triangle (QuadraticPoisson.reference μ α) P (QuadraticPoisson.reference ν α)
  have hsym : SignedAtomicDistance.distance (QuadraticPoisson.reference μ α) P =
      SignedAtomicDistance.distance P (QuadraticPoisson.reference μ α) := by
    unfold SignedAtomicDistance.distance
    exact tsum_congr fun _ ↦ abs_sub_comm _ _
  rw [hsym] at hr
  constructor <;> nlinarith only [hlo, hup, ht, hr, herror]

end PaperP1.QuadraticMeanLawComparison
