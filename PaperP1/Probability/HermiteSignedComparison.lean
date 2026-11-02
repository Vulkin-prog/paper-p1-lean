module

public import PaperP1.Probability.HermiteReference
public import PaperP1.Probability.AtomicProbabilityMetric

/-! # Actual signed-measure comparison of Hermite and quadratic references -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HermiteSignedComparison

open PaperP1.CompletedLaw PaperP1.CompletedLawShift PaperP1.HermiteReference

theorem singleton_difference (μ α : ℝ) (k : ℕ) :
    (toSignedMeasure (reference μ α) - QuadraticPoisson.reference μ α) {k} =
      coeff k (reference μ α - quadratic μ α) := by
  rw [← quadratic_actual_signed_measure μ α, _root_.sub_apply,
    toSignedMeasure_singleton, toSignedMeasure_singleton, map_sub]

theorem actual_signed_error (μ α : ℝ) (hμ : 0 ≤ μ) :
    (∑' k : ℕ, |(toSignedMeasure (reference μ α) - QuadraticPoisson.reference μ α) {k}|) ≤
      4 * α ^ 2 * Real.exp (2 * |α|) := by
  simp_rw [singleton_difference]
  exact (tsum_abs_coeff_le _).trans (norm_error hμ α)

theorem actual_signed_error_symmetric (μ α : ℝ) (hμ : 0 ≤ μ) :
    (∑' k : ℕ, |(QuadraticPoisson.reference μ α - toSignedMeasure (reference μ α)) {k}|) ≤
      4 * α ^ 2 * Real.exp (2 * |α|) := by
  have heq (k : ℕ) :
      |(QuadraticPoisson.reference μ α - toSignedMeasure (reference μ α)) {k}| =
        |(toSignedMeasure (reference μ α) - QuadraticPoisson.reference μ α) {k}| := by
    rw [_root_.sub_apply, _root_.sub_apply, abs_sub_comm]
  simp_rw [heq]
  exact actual_signed_error μ α hμ

end PaperP1.HermiteSignedComparison
