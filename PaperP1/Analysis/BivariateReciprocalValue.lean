module

public import PaperP1.Analysis.BivariateSeriesOperations
public import PaperP1.Arithmetic.BiquadraticNumeratorFactor
public import PaperP1.Algebra.BivariateEvaluation

/-! # The actual reciprocal-polynomial branch value agrees with polynomial evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateReciprocalValue

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateReciprocalSeries
  PaperP1.BivariateReciprocalProduct PaperP1.BiquadraticFormalNumerator
  PaperP1.BivariateSeriesValue PaperP1.BivariateSeriesOperations

theorem reciprocal_mul_sum (P : ℤ[X][X]) (a b : ℕ) (f : Series) :
    reciprocal P a b * f = ∑ i : Fin (a + 1) × Fin (b + 1),
      PowerSeries.C (PowerSeries.C ((P.coeff i.2.val).coeff i.1.val : ℚ)) *
        shift (a - i.1.val) (b - i.2.val) f := by
  rw [reciprocal_sum, sum_mul]
  apply sum_congr rfl
  intro i _
  unfold shift
  rw [map_pow]
  ring

theorem reciprocal_branch_summable {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (P : ℤ[X][X]) (a b : ℕ) (ξ η : ℝ)
    (hγ : ∀ i, |(γ i : ℝ) * ξ| < 1) (hδ : ∀ i, |(δ i : ℝ) * η| < 1) :
    AbsolutelySummable (reciprocal P a b * branch γ δ) ξ η := by
  rw [reciprocal_mul_sum]
  apply absolutelySummable_sum
  intro i _
  exact absolutelySummable_scalar _ _ ξ η
    (absolutelySummable_shift _ _ _ ξ η (branch_summable γ δ ξ η hγ hδ))

theorem value_reciprocal_branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (P : ℤ[X][X]) (a b : ℕ) (ξ η : ℝ)
    (hγ : ∀ i, |(γ i : ℝ) * ξ| < 1) (hδ : ∀ i, |(δ i : ℝ) * η| < 1) :
    value (reciprocal P a b * branch γ δ) ξ η =
      (∑ i : Fin (a + 1) × Fin (b + 1), ((P.coeff i.2.val).coeff i.1.val : ℝ) *
        ξ ^ (a - i.1.val) * η ^ (b - i.2.val)) * value (branch γ δ) ξ η := by
  have hb := branch_summable γ δ ξ η hγ hδ
  rw [reciprocal_mul_sum, value_sum univ _ ξ η
    (fun i _ ↦ absolutelySummable_scalar _ _ ξ η (absolutelySummable_shift _ _ _ ξ η hb)), sum_mul]
  apply sum_congr rfl
  intro i _
  rw [value_scalar, value_shift _ _ _ ξ η hb]
  push_cast
  ring

theorem scaled_reciprocal_branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (P : ℤ[X][X]) (a b : ℕ) (hxP : degreeX P ≤ a) (hyP : degreeY P ≤ b)
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hγ : ∀ i, |(γ i : ℝ) * (1 / x)| < 1) (hδ : ∀ i, |(δ i : ℝ) * (1 / y)| < 1) :
    x ^ a * y ^ b * value (reciprocal P a b * branch γ δ) (1 / x) (1 / y) =
      BivariateEvaluation.evaluate x y P * value (branch γ δ) (1 / x) (1 / y) := by
  rw [value_reciprocal_branch γ δ P a b (1 / x) (1 / y) hγ hδ, ← mul_assoc,
    BivariateEvaluation.reciprocal_sum_scaled P a b hxP hyP x y hx hy]

end PaperP1.BivariateReciprocalValue
