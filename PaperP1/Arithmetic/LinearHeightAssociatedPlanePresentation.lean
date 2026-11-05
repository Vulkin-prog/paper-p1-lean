module

public import PaperP1.Arithmetic.LinearHeightCurveBudget
public import PaperP1.Algebra.RationalAssociatedIntegerFactor
public import PaperP1.Arithmetic.SmallHeightAssociatedPlanePresentation
public import PaperP1.Algebra.HomogenizationIrreducibilityReflection

/-! # An associated actual curve with height exponent linear in its degree

Wide interpolation, the exact finite Bezout threshold and integer factor
selection are all supplied before applying the proved factor-height estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHeightAssociatedPlanePresentation

open Polynomial Finset PolynomialScalarProjection RationalBivariateIrreducibility
  GeometricFactorSwap

theorem associated_degree (F G : ℚ[X][X]) (hF : F ≠ 0) (h : Associated F G) :
    PlaneCurvePointCount.degree F = PlaneCurvePointCount.degree G := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ManyPointsScalarDescent.degree_mul F (u : ℚ[X][X]) hF u.ne_zero,
    IntegerCurveRationalization.degree_of_isUnit _ u.isUnit, add_zero]

theorem exists_presentation (D N B : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hB : 1 ≤ B) (hBN : B ≤ (D + 1) * N)
    (F : ℚ[X][X]) (hF : Irreducible F) (hgeo : Irreducible (extend F : ℂ[X][X]))
    (hdegree : PlaneCurvePointCount.degree F = D) (S : Finset (ℤ × ℤ))
    (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, F.evalEval (z.1 : ℚ) (z.2 : ℚ) = 0)
    (hmany : 4 * D ^ 2 < S.card) :
    ∃ C : ℤ[X][X], Irreducible C ∧ Geometric C ∧ Associated F (rationalize C) ∧
      PlaneCurvePointCount.degree C = D ∧ BivariateHeight.height C ≤ N ^ (256 * D) ∧
      ∀ z ∈ S, C.evalEval z.1 z.2 = 0 := by
  classical
  have houter : F.natDegree ≤ D := (BivariateResultantDegree.outer_degree_le F).trans hdegree.le
  have hinner (y : ℕ) : (F.coeff y).natDegree ≤ D := by
    by_cases hz : F.coeff y = 0
    · simp only [hz, Polynomial.natDegree_zero, Nat.zero_le]
    · have hh := (BivariateResultantDegree.coefficient_row_degree F y hz).trans hdegree.le
      omega
  obtain ⟨Q, hQne, _hQouter, _hQinner, hQdegree, hQheight, hQzero⟩ :=
    WidePlaneInterpolation.exists_bounded_equation D B hB F hF.ne_zero houter hinner S hbox hzero
  have hdQ : PlaneCurvePointCount.degree (rationalize Q) ≤ 4 * D := by
    have hh : PlaneCurvePointCount.degree (rationalize Q) = PlaneCurvePointCount.degree Q :=
      IntegerCurveRationalization.degree_coefficientMap (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ)) Q
    exact hh.le.trans hQdegree
  have hdiv : F ∣ rationalize Q := by
    by_contra hn
    let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
    have hi : Function.Injective f := by
      intro z w he
      exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
        (Int.cast_injective (congrArg Prod.snd he))
    have hb := FinitePlaneBezout.common_points_card F (rationalize Q) hF hn (S.image f) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      refine ⟨hzero w hw, ?_⟩
      rw [SmallHeightAssociatedPlanePresentation.rationalized_evaluation, hQzero w hw, Int.cast_zero])
    rw [card_image_of_injective _ hi, hdegree] at hb
    have hbound : S.card ≤ 4 * D ^ 2 := hb.trans
      ((Nat.mul_le_mul_left D hdQ).trans_eq (by ring))
    omega
  obtain ⟨C, hC, hCQ, hassoc⟩ := RationalAssociatedIntegerFactor.exists_integer_factor F hF Q hQne hdiv
  have hassoc' : Associated F (rationalize C) := hassoc
  have hAbsC : Irreducible (extend (rationalize C) : ℂ[X][X]) := by
    let φ := Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    exact (Associated.map φ hassoc').irreducible hgeo
  have hCgeo : Geometric C :=
    (HomogenizationIrreducibilityReflection.geometric_iff_affine C hC.ne_zero).mpr (by
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hAbsC)
  have hCdegree : PlaneCurvePointCount.degree C = D := by
    have hh := associated_degree F (rationalize C) hF.ne_zero hassoc'
    have hmap : PlaneCurvePointCount.degree (rationalize C) = PlaneCurvePointCount.degree C :=
      IntegerCurveRationalization.degree_coefficientMap (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ)) C
    rw [hmap] at hh
    exact hh.symm.trans hdegree
  refine ⟨C, hC, hCgeo, hassoc', hCdegree,
    LinearHeightCurveBudget.factor_height_power D N B hD hDN hBN Q C hQne hCQ hQdegree hQheight, ?_⟩
  intro z hz
  have he := (Associated.map (Polynomial.evalEvalRingHom (z.1 : ℚ) (z.2 : ℚ)) hassoc').eq_zero_iff
  have hh := he.mp (hzero z hz)
  change (rationalize C).evalEval (z.1 : ℚ) (z.2 : ℚ) = 0 at hh
  rw [SmallHeightAssociatedPlanePresentation.rationalized_evaluation] at hh
  exact_mod_cast hh

end PaperP1.LinearHeightAssociatedPlanePresentation
