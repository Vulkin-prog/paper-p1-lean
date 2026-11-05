module

public import PaperP1.Algebra.ScalarComponentPoints
public import PaperP1.Algebra.FinitePlaneBezout
public import PaperP1.Algebra.ScalarIrreducibilityReflection
public import PaperP1.Arithmetic.IntegerCurveRationalization
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # More than the degree square of base-field points forces scalar descent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ManyPointsScalarDescent

open Polynomial Finset PaperP1.PolynomialScalarProjection

theorem degree_mul {F : Type*} [Field F] (P Q : F[X][X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    PlaneCurvePointCount.degree (P * Q) = PlaneCurvePointCount.degree P + PlaneCurvePointCount.degree Q := by
  let e := BivariateTotalDegreeChart.chart F
  have hP' : e.symm P ≠ 0 := by
    intro hz
    apply hP
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg e hz
  have hQ' : e.symm Q ≠ 0 := by
    intro hz
    apply hQ
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg e hz
  have hd (A : F[X][X]) : PlaneCurvePointCount.degree A = (e.symm A).totalDegree := by
    rw [← BivariateTotalDegreeChart.chart_degree, AlgEquiv.apply_symm_apply]
  rw [hd, hd P, hd Q, map_mul]
  exact MvPolynomial.totalDegree_mul_of_isDomain hP' hQ'

theorem unit_of_degree_zero {F : Type*} [Field F] (P : F[X][X]) (hP : P ≠ 0)
    (hd : PlaneCurvePointCount.degree P = 0) : IsUnit P := by
  have hout : P.natDegree = 0 := by
    have hh := BivariateResultantDegree.outer_degree_le P
    omega
  have he := Polynomial.eq_C_of_natDegree_eq_zero hout
  have hrow : P.coeff 0 ≠ 0 := by
    intro hz
    apply hP
    simpa only [hz, map_zero] using he
  have hh := BivariateResultantDegree.coefficient_row_degree P 0 hrow
  have hin : (P.coeff 0).natDegree = 0 := by omega
  have hi := Polynomial.eq_C_of_natDegree_eq_zero hin
  have hc : (P.coeff 0).coeff 0 ≠ 0 := by
    intro hz
    apply hrow
    simpa only [hz, map_zero] using hi
  rw [he, hi]
  exact Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))

theorem divisor_associated {F : Type*} [Field F] (P Q : F[X][X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : PlaneCurvePointCount.degree Q ≤ PlaneCurvePointCount.degree P) (hdiv : P ∣ Q) :
    Associated P Q ∧ PlaneCurvePointCount.degree Q = PlaneCurvePointCount.degree P := by
  obtain ⟨A, hA⟩ := hdiv
  have hAne : A ≠ 0 := by
    intro hz
    apply hQ
    rw [hA, hz, mul_zero]
  have he := degree_mul P A hP hAne
  rw [← hA] at he
  have hdA : PlaneCurvePointCount.degree A = 0 := by omega
  refine ⟨?_, by omega⟩
  rw [hA]
  exact associated_mul_unit_right P A (unit_of_degree_zero A hAne hdA)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]

theorem components_divide_of_many_points (P : L[X][X]) (hP : Irreducible P)
    (S : Finset (K × K))
    (hS : ∀ z ∈ S, P.evalEval (algebraMap K L z.1) (algebraMap K L z.2) = 0)
    (hmany : PlaneCurvePointCount.degree P ^ 2 < S.card) (ell : L →ₗ[K] K) :
    P ∣ (extend (component ell P) : L[X][X]) := by
  classical
  by_contra hnot
  let f : K × K → L × L := fun z ↦ (algebraMap K L z.1, algebraMap K L z.2)
  have hi : Function.Injective f := by
    intro z w he
    exact Prod.ext ((algebraMap K L).injective (congrArg Prod.fst he))
      ((algebraMap K L).injective (congrArg Prod.snd he))
  have hc := FinitePlaneBezout.common_points_card P (extend (component ell P)) hP hnot (S.image f) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    refine ⟨hS w hw, ?_⟩
    have he := Polynomial.map_mapRingHom_evalEval (algebraMap K L) (component ell P) w.1 w.2
    rw [ScalarComponentPoints.components_vanish ell P w.1 w.2 (hS w hw), map_zero] at he
    exact he)
  have hd : PlaneCurvePointCount.degree (extend (component ell P) : L[X][X]) =
      PlaneCurvePointCount.degree (component ell P) :=
    IntegerCurveRationalization.degree_coefficientMap _ (algebraMap K L).injective _
  rw [card_image_of_injective _ hi, hd] at hc
  have hb := hc.trans (Nat.mul_le_mul_left _ (ScalarComponentPoints.component_degree ell P))
  rw [← pow_two] at hb
  omega

theorem many_points_descent (P : L[X][X]) (hP : Irreducible P) (S : Finset (K × K))
    (hS : ∀ z ∈ S, P.evalEval (algebraMap K L z.1) (algebraMap K L z.2) = 0)
    (hmany : PlaneCurvePointCount.degree P ^ 2 < S.card) :
    ∃ Q : K[X][X], Irreducible Q ∧ Associated P (extend Q : L[X][X]) ∧
      PlaneCurvePointCount.degree Q = PlaneCurvePointCount.degree P ∧
        ∀ z ∈ S, Q.evalEval z.1 z.2 = 0 := by
  obtain ⟨ell, hell⟩ := ScalarComponentPoints.exists_nonzero_component (K := K) P hP.ne_zero
  let Q := component ell P
  have hi : Function.Injective (IntegerCurveRationalization.coefficientMap (algebraMap K L)) :=
    IntegerCurveRationalization.coefficientMap_injective _ (algebraMap K L).injective
  have hQ : (extend Q : L[X][X]) ≠ 0 := by
    intro hz
    apply hell
    apply hi
    exact hz.trans (map_zero _).symm
  have hd : PlaneCurvePointCount.degree (extend Q : L[X][X]) = PlaneCurvePointCount.degree Q :=
    IntegerCurveRationalization.degree_coefficientMap _ (algebraMap K L).injective _
  obtain ⟨hassoc, heq⟩ := divisor_associated P (extend Q) hP.ne_zero hQ
    (by rw [hd]; exact ScalarComponentPoints.component_degree ell P)
    (components_divide_of_many_points P hP S hS hmany ell)
  refine ⟨Q, ScalarIrreducibilityReflection.irreducible_of_extension Q (hassoc.irreducible hP),
    hassoc, hd.symm.trans heq, ?_⟩
  intro z hz
  exact ScalarComponentPoints.components_vanish ell P z.1 z.2 (hS z hz)

end PaperP1.ManyPointsScalarDescent
