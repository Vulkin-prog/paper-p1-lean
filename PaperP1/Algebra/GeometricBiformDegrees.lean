module

public import PaperP1.Algebra.HomogenizationIrreducibilityReflection
public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Arithmetic.IntegerCurveRationalization
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Geometric plane curves of total degree at least two have both partial degrees positive -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricBiformDegrees

open Polynomial

theorem constant_outer_degree {R : Type*} [CommRing R] (A : R[X]) (hA : A ≠ 0) :
    PlaneCurvePointCount.degree (C A) = A.natDegree := by
  simp only [PlaneCurvePointCount.degree, Polynomial.support_C hA, Finset.sup_singleton,
    Polynomial.coeff_C_zero, zero_add]

theorem constant_irreducible_reflection {R : Type*} [CommRing R] (A : R[X])
    (hA : Irreducible (C A : R[X][X])) : Irreducible A := by
  refine ⟨fun hu ↦ hA.1 (hu.map Polynomial.C), ?_⟩
  intro B D hBD
  have he : (C A : R[X][X]) = C B * C D := by rw [hBD, map_mul]
  rcases hA.2 he with hB | hD
  · left
    simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using hB.map (Polynomial.evalRingHom 0)
  · right
    simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using hD.map (Polynomial.evalRingHom 0)

theorem univariate_degree_one {F : Type*} [Field F] [IsAlgClosed F]
    (P : F[X][X]) (hP : Irreducible P) (houter : P.natDegree = 0) :
    PlaneCurvePointCount.degree P = 1 := by
  have he := Polynomial.eq_C_of_natDegree_eq_zero houter
  have hA : Irreducible (P.coeff 0) := constant_irreducible_reflection _ (by rwa [← he])
  have hdeg : (P.coeff 0).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible F hA)
  rw [he, constant_outer_degree _ hA.ne_zero]
  exact hdeg

theorem outer_degree_pos {F : Type*} [Field F] [IsAlgClosed F]
    (P : F[X][X]) (hP : Irreducible P) (hD : 2 ≤ PlaneCurvePointCount.degree P) : 0 < P.natDegree := by
  by_contra hn
  have hd := univariate_degree_one P hP (by omega)
  omega

theorem positive_partial_degrees {F : Type*} [Field F] [IsAlgClosed F]
    (P : F[X][X]) (hP : Irreducible P) (hD : 2 ≤ PlaneCurvePointCount.degree P) :
    0 < (Bivariate.swap P).natDegree ∧ 0 < P.natDegree := by
  refine ⟨?_, outer_degree_pos P hP hD⟩
  apply outer_degree_pos (Bivariate.swap P) ((MulEquiv.irreducible_iff Bivariate.swap).mpr hP)
  rwa [BivariateCurveDegreeTransport.degree_swap]

theorem integer_outer_degree_pos (G : ℤ[X][X]) (hne : G ≠ 0)
    (hG : GeometricFactorSwap.Geometric G) (hD : 2 ≤ PlaneCurvePointCount.degree G) :
    0 < BivariateDegrees.degreeY G := by
  let P := ComplexProjectiveIrreducibility.complexAffine G
  have hP : Irreducible P := (HomogenizationIrreducibilityReflection.geometric_iff_affine G hne).mp hG
  have hd : PlaneCurvePointCount.degree P = PlaneCurvePointCount.degree G :=
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective G
  have hp := outer_degree_pos P hP (by rw [hd]; exact hD)
  have he : P.natDegree = BivariateDegrees.degreeY G :=
    Polynomial.natDegree_map_eq_of_injective
      (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective) G
  exact he ▸ hp

theorem integer_positive_degrees (G : ℤ[X][X]) (hne : G ≠ 0)
    (hG : GeometricFactorSwap.Geometric G) (hD : 2 ≤ PlaneCurvePointCount.degree G) :
    0 < BivariateDegrees.degreeX G ∧ 0 < BivariateDegrees.degreeY G := by
  refine ⟨?_, integer_outer_degree_pos G hne hG hD⟩
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hne
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hh := integer_outer_degree_pos (Bivariate.swap G) hswap (GeometricFactorSwap.geometric_swap G hG)
    (by rwa [BivariateCurveDegreeTransport.degree_swap])
  exact hh

end PaperP1.GeometricBiformDegrees
