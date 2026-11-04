module

public import PaperP1.Arithmetic.BiformCoefficientRecovery
public import PaperP1.Algebra.IntegerBivariateFactorCover

/-! # Actual projective equations of arbitrary integer bivariate factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerFactorProjectiveCurve

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.DeterminantIntegerRows
  PaperP1.DeterminantAuxiliaryBiform PaperP1.TwoKernelDeterminantBoxes
  PaperP1.BivariateEvaluation

def coefficients (F : ℤ[X][X]) : Exponent (degreeX F) (degreeY F) → ℤ :=
  fun i ↦ (F.coeff i.2.val).coeff i.1.val

def projective (F : ℤ[X][X]) : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℤ) :=
  biform (degreeX F) (degreeY F) (coefficients F)

theorem reconstruction (F : ℤ[X][X]) :
    rectangle (degreeX F) (degreeY F) (coefficients F) = F :=
  BivariateReciprocalProduct.rectangle_reconstruction F _ _ le_rfl le_rfl

theorem coefficients_nonzero (F : ℤ[X][X]) (hF : F ≠ 0) : coefficients F ≠ 0 := by
  intro hw
  apply hF
  have h := reconstruction F
  rw [hw] at h
  simpa [rectangle, row] using h.symm

theorem coefficient_height (F : ℤ[X][X]) : ∀ i, |coefficients F i| ≤ (height F : ℤ) := by
  intro i
  rw [← Int.natCast_natAbs]
  exact_mod_cast coefficient_natAbs_le_height F i.2.val i.1.val

theorem projective_nonzero (F : ℤ[X][X]) (hF : F ≠ 0) : projective F ≠ 0 :=
  biform_nonzero _ _ _ (coefficients_nonzero F hF)

theorem projective_height (F : ℤ[X][X]) :
    ∀ m n, |((projective F).coeff m).coeff n| ≤ (height F : ℤ) :=
  biform_coefficient_bound _ _ _ _ (coefficient_height F)

theorem projective_homogeneous (F : ℤ[X][X]) : (projective F).IsHomogeneous (degreeX F) :=
  biform_homogeneous _ _ _

theorem coefficient_forms_homogeneous (F : ℤ[X][X]) :
    ∀ a, (forms (degreeX F) (degreeY F) (coefficients F) a).IsHomogeneous (degreeY F) :=
  forms_homogeneous _ _ _

theorem rectangle_evaluation_clearing (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad)
    (he : 0 < p.1.2) (hu : 0 < p.2.1) :
    ((MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
        (biform A B w) : ℤ) : ℚ) =
      denominator A B p * evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) (rectangle A B w) := by
  rw [biform_eval_original, original_integer_rows, row_sum_clearing A B w p he hu, rectangle_evaluation]
  congr 1
  apply sum_congr rfl
  intro i _
  unfold rationalEntry
  ring

theorem rectangle_zero_iff (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad)
    (he : 0 < p.1.2) (hu : 0 < p.2.1) :
    MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
        (biform A B w) = 0 ↔
      evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) (rectangle A B w) = 0 := by
  have hc := rectangle_evaluation_clearing A B w p he hu
  constructor
  · intro hz
    rw [hz, Int.cast_zero] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left (denominator_pos A B p he hu).ne'
  · intro hz
    rw [hz, mul_zero] at hc
    exact_mod_cast hc

theorem projective_zero_iff (F : ℤ[X][X]) (p : Quad) (he : 0 < p.1.2) (hu : 0 < p.2.1) :
    MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
        (projective F) = 0 ↔ evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0 := by
  simpa only [projective, reconstruction] using rectangle_zero_iff _ _ (coefficients F) p he hu

end PaperP1.IntegerFactorProjectiveCurve
