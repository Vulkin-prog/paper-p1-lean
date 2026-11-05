module

public import PaperP1.Algebra.BivariateIrreducibleHomogenization
public import PaperP1.Algebra.SmoothPointAbsoluteIrreducibility
public import PaperP1.Diophantine.NonGeometricRationalSingularity

/-! # The actual complex projective polynomial and the non-geometric point input

The coefficientwise identification links the actual biform to the checked
double homogenization. The non-geometric numerical input is then proved,
without a counting premise or an unproved rational-singularity argument.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComplexProjectiveIrreducibility

open Polynomial PaperP1.BivariateDegrees PaperP1.RationalBivariateIrreducibility
  PaperP1.GeometricFactorSwap

def complexAffine (G : ℤ[X][X]) : ℂ[X][X] :=
  G.map (Polynomial.mapRingHom (Int.castRingHom ℂ))

theorem coefficient_cast (G : ℤ[X][X]) (i j : ℕ) :
    ((complexAffine G).coeff i).coeff j = ((G.coeff i).coeff j : ℂ) := by
  simp only [complexAffine, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Int.coe_castRingHom]

theorem outer_degree (G : ℤ[X][X]) : (complexAffine G).natDegree = degreeY G := by
  unfold complexAffine degreeY
  have hinj : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℂ)) :=
    Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  exact Polynomial.natDegree_map_eq_of_injective hinj G

theorem swap_naturality (G : ℤ[X][X]) :
    Bivariate.swap (complexAffine G) = complexAffine (Bivariate.swap G) := by
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  rw [PaperP1.BivariateIrreducibleHomogenization.swap_coefficient, coefficient_cast,
    coefficient_cast, PaperP1.BivariateIrreducibleHomogenization.swap_coefficient]

theorem inner_degree (G : ℤ[X][X]) :
    (Bivariate.swap (complexAffine G)).natDegree = degreeX G := by
  rw [swap_naturality]
  exact outer_degree (Bivariate.swap G)

theorem rational_extension (G : ℤ[X][X]) :
    PaperP1.PolynomialScalarProjection.extend (L := ℂ) (rationalize G) = complexAffine G := by
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  simp [PaperP1.PolynomialScalarProjection.extend, rationalize, complexAffine]

theorem projective_identity (G : ℤ[X][X]) :
    complexProjective G = PaperP1.BivariateIrreducibleHomogenization.bihomogenize (complexAffine G) := by
  apply MvPolynomial.ext
  intro m
  apply MvPolynomial.ext
  intro n
  rw [PaperP1.GeometricFactorSwap.complex_coefficient,
    PaperP1.ProjectiveFactorCoefficients.projective_coefficient,
    PaperP1.BivariateIrreducibleHomogenization.bihomogenize_coefficient,
    inner_degree, outer_degree, coefficient_cast]
  by_cases h : m 0 + m 1 = degreeX G ∧ n 0 + n 1 = degreeY G <;> simp [h]

theorem geometric_of_affine (G : ℤ[X][X]) (hG : Irreducible (complexAffine G)) : Geometric G := by
  unfold Geometric
  rw [projective_identity]
  exact PaperP1.BivariateIrreducibleHomogenization.bihomogenize_irreducible _ hG

theorem singularity_input : PaperP1.NonGeometricRationalSingularity.Input := by
  intro G _hX hY hG hnot x z hz
  by_contra hd
  have hdeg : 0 < (rationalize G).natDegree :=
    (PaperP1.RationalizedCriticalPointBound.outer_degree G).symm ▸ hY
  have hCA : Irreducible (complexAffine G) := by
    rw [← rational_extension G]
    exact PaperP1.SmoothPointAbsoluteIrreducibility.smooth_point_irreducible (L := ℂ)
      (rationalize G) hG hdeg x z hz hd
  exact hnot (geometric_of_affine G hCA)

theorem nongeometric_input : PaperP1.NonGeometricBiformInput.Input :=
  PaperP1.NonGeometricRationalSingularity.nongeometric_input_of_singularity singularity_input

end PaperP1.ComplexProjectiveIrreducibility
