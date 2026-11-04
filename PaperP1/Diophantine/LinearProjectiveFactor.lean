module

public import PaperP1.Algebra.LinearBivariateCoefficients
public import PaperP1.Arithmetic.IntegerFactorProjectiveCurve

/-! # Exact linear projective equation of the actual first-degree-one factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearProjectiveFactor

open Polynomial PaperP1.BivariateDegrees PaperP1.LinearBivariateCoefficients
open PaperP1.BiquadraticCoefficientPolynomials PaperP1.IntegerFactorProjectiveCurve
open PaperP1.DeterminantAuxiliaryBiform PaperP1.HomogeneousCharts

theorem row_eq_swapped_coefficient (G : ℤ[X][X]) (i : ℕ) :
    row (degreeY G) (fun j ↦ (G.coeff j.val).coeff i) = (Bivariate.swap G).coeff i := by
  have hd : ((Bivariate.swap G).coeff i).natDegree ≤ degreeY G := by
    simpa only [degreeX, degreeY, Bivariate.swap_swap_apply] using
      natDegree_coeff_le_degreeX (Bivariate.swap G) i
  convert BivariateReciprocalProduct.row_reconstruction ((Bivariate.swap G).coeff i) (degreeY G) hd using 1
  congr 1
  funext j
  exact (coeff_swap G j.val i).symm

theorem forms_eq_swapped_homogenize (G : ℤ[X][X]) (i : Fin (degreeX G + 1)) :
    forms (degreeX G) (degreeY G) (coefficients G) i =
      ((Bivariate.swap G).coeff i.val).homogenize (degreeY G) := by
  unfold forms coefficients
  change (row (degreeY G) (fun b ↦ (G.coeff b.val).coeff i.val)).homogenize (degreeY G) = _
  rw [row_eq_swapped_coefficient]

theorem projective_chart_coefficient (G : ℤ[X][X]) (i : Fin (degreeX G + 1)) :
    (chart (projective G)).coeff i.val = ((Bivariate.swap G).coeff i.val).homogenize (degreeY G) := by
  rw [projective, biform_chart_coefficient, forms_eq_swapped_homogenize]

theorem projective_linear (G : ℤ[X][X]) (hG : degreeX G = 1) :
    projective G =
      MvPolynomial.C ((firstCoefficient G).homogenize (degreeY G)) * MvPolynomial.X 0 +
      MvPolynomial.C ((secondCoefficient G).homogenize (degreeY G)) * MvPolynomial.X 1 := by
  have hhom : (projective G).IsHomogeneous 1 := by simpa only [hG] using projective_homogeneous G
  have h0 := projective_chart_coefficient G ⟨0, by omega⟩
  have h1 := projective_chart_coefficient G ⟨1, by omega⟩
  have he := BihomogeneousSwap.binary_expansion (projective G) hhom
  change projective G = ∑ j : Fin 2, MvPolynomial.C ((chart (projective G)).coeff j.val) *
    MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (1 - j.val) at he
  norm_num [Fin.sum_univ_two, h0, h1] at he
  simpa only [firstCoefficient, secondCoefficient, add_comm] using he

theorem evaluation_linear (G : ℤ[X][X]) (hG : degreeX G = 1) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) =
      x 0 * MvPolynomial.eval y ((firstCoefficient G).homogenize (degreeY G)) +
      x 1 * MvPolynomial.eval y ((secondCoefficient G).homogenize (degreeY G)) := by
  rw [projective_linear G hG]
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X]
  ring

end PaperP1.LinearProjectiveFactor
