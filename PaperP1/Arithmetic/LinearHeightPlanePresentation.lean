module

public import PaperP1.Arithmetic.DegreeUniformPlanePresentation
public import PaperP1.Arithmetic.LinearHeightAssociatedPlanePresentation

/-! # A bounded shear followed by an associated linear-height integer equation

The original coefficients are unrestricted. The population, height budget,
exact degree and full outer degree are retained under one actual shear.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHeightPlanePresentation

open Polynomial Finset RationalBivariateIrreducibility GeometricFactorSwap PolynomialScalarProjection
  DegreeUniformPlanePresentation

theorem exists_presentation (P : ℤ[X][X]) (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hdegree : PlaneCurvePointCount.degree P = D) (hgeo : Geometric P)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N)
    (hmany : 4 * D ^ 2 < S.card) :
    ∃ t : ℕ, t ≤ D ∧ ∃ Q : ℤ[X][X], Irreducible Q ∧ PlaneCurvePointCount.degree Q = D ∧
      Q.natDegree = D ∧ Geometric Q ∧ BivariateHeight.height Q ≤ N ^ (256 * D) ∧
      Associated (rationalize (BivariateLinearShear.shear (t : ℤ) P)) (rationalize Q) ∧
      ∀ z ∈ S, Q.evalEval (IntegerPlaneShear.point (t : ℤ) z).1
        (IntegerPlaneShear.point (t : ℤ) z).2 = 0 := by
  classical
  have hne : P ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree P = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨t, ht, hout⟩ := BoundedPlaneShear.exists_full_outer_degree P hne
  rw [hdegree] at ht hout
  let R := BivariateLinearShear.shear (t : ℤ) P
  have hRdegree : PlaneCurvePointCount.degree R = D :=
    (BivariateLinearShear.shear_degree (t : ℤ) P).trans hdegree
  have hRgeo : Geometric R := IntegerPlaneShear.geometric (t : ℤ) P hne hgeo
  have hRne : R ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree R = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  have hRF : Irreducible (rationalize R) :=
    ScalarIrreducibilityReflection.geometric_rational_irreducible R hRne hRgeo
  have hAbs : Irreducible (extend (rationalize R) : ℂ[X][X]) := by
    rw [ComplexProjectiveIrreducibility.rational_extension]
    exact (HomogenizationIrreducibilityReflection.geometric_iff_affine R hRne).mp hRgeo
  let H := (D + 1) * N
  let U := S.image (IntegerPlaneShear.point (t : ℤ))
  have hHpos : 0 < H := Nat.mul_pos (by omega) (by omega)
  have hUcard : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
  have hbox : ∀ z ∈ U, z.1.natAbs ≤ H ∧ z.2.natAbs ≤ H := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact point_natAbs_bounds D t ht N z (hS z hz).2.1 (hS z hz).2.2
  have hzero : ∀ z ∈ U, R.evalEval z.1 z.2 = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact IntegerPlaneShear.point_zero (t : ℤ) P z (hS z hz).1
  have hRFdegree : PlaneCurvePointCount.degree (rationalize R) = D := by
    have hh : PlaneCurvePointCount.degree (rationalize R) = PlaneCurvePointCount.degree R :=
      IntegerCurveRationalization.degree_coefficientMap (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ)) R
    exact hh.trans hRdegree
  have hzRat (z : ℤ × ℤ) (hz : z ∈ U) : (rationalize R).evalEval (z.1 : ℚ) (z.2 : ℚ) = 0 := by
    rw [SmallHeightAssociatedPlanePresentation.rationalized_evaluation, hzero z hz, Int.cast_zero]
  obtain ⟨Q, hQ, hQgeo, hassoc, hQdegree, hheight, hQzero⟩ :=
    LinearHeightAssociatedPlanePresentation.exists_presentation D N H hD hDN (by omega) le_rfl
      (rationalize R) hRF hAbs hRFdegree U hbox hzRat (by rw [hUcard]; exact hmany)
  have hQr : Irreducible (rationalize Q) := hassoc.irreducible hRF
  have houter₁ := Polynomial.natDegree_le_of_dvd hassoc.dvd hQr.ne_zero
  have houter₂ := Polynomial.natDegree_le_of_dvd hassoc.symm.dvd hRF.ne_zero
  rw [RationalizedCriticalPointBound.outer_degree, RationalizedCriticalPointBound.outer_degree] at houter₁ houter₂
  have houter : Q.natDegree = D := by
    have hh := Nat.le_antisymm houter₂ houter₁
    change Q.natDegree = R.natDegree at hh
    exact hh.trans hout
  refine ⟨t, ht, Q, hQ, hQdegree, houter, hQgeo, hheight, hassoc, ?_⟩
  intro z hz
  exact hQzero _ (mem_image_of_mem _ hz)

end PaperP1.LinearHeightPlanePresentation
