module

public import PaperP1.Arithmetic.IntegralGeometricPlanePointInput
public import PaperP1.Arithmetic.BoundedPlaneInterpolation

/-! # A constructed bounded-height equation associated to the entire original curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallHeightAssociatedPlanePresentation

open Polynomial Finset PaperP1.PolynomialScalarProjection
open PaperP1.RationalBivariateIrreducibility

theorem rationalized_evaluation (F : ℤ[X][X]) (z : ℤ × ℤ) :
    (rationalize F).evalEval (z.1 : ℚ) (z.2 : ℚ) = ((F.evalEval z.1 z.2 : ℤ) : ℚ) :=
  Polynomial.map_mapRingHom_evalEval (Int.castRingHom ℚ) F z.1 z.2

theorem grid_eq_of_associated (F Q : ℤ[X][X])
    (h : Associated (rationalize F) (rationalize Q)) (B : ℕ) :
    PlaneCurvePointCount.grid F B = PlaneCurvePointCount.grid Q B := by
  classical
  ext z
  have he := (Associated.map (Polynomial.evalEvalRingHom (z.1 : ℚ) (z.2 : ℚ)) h).eq_zero_iff
  change (rationalize F).evalEval (z.1 : ℚ) (z.2 : ℚ) = 0 ↔
    (rationalize Q).evalEval (z.1 : ℚ) (z.2 : ℚ) = 0 at he
  rw [rationalized_evaluation F z, rationalized_evaluation Q z] at he
  have hz : F.evalEval z.1 z.2 = 0 ↔ Q.evalEval z.1 z.2 = 0 := by exact_mod_cast he
  simp only [PlaneCurvePointCount.mem_grid, Int.cast_id, hz]

theorem exists_presentation (F : ℤ[X][X]) (hF : Irreducible (rationalize F))
    (hgeo : Irreducible (extend (rationalize F) : ℂ[X][X])) (B : ℕ) (hB : 1 ≤ B)
    (S : Finset (ℤ × ℤ)) (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, F.evalEval z.1 z.2 = 0)
    (hmany : PlaneCurvePointCount.degree F ^ 2 < S.card) :
    ∃ Q : ℤ[X][X], Irreducible (rationalize Q) ∧
      Irreducible (extend (rationalize Q) : ℂ[X][X]) ∧
      Associated (rationalize F) (rationalize Q) ∧
      PlaneCurvePointCount.degree Q = PlaneCurvePointCount.degree F ∧
      BivariateHeight.height Q ≤ BoundedPlaneInterpolation.heightBound (PlaneCurvePointCount.degree F) B ∧
      ∀ z ∈ S, Q.evalEval z.1 z.2 = 0 := by
  classical
  have hne : F ≠ 0 := by
    intro hz
    apply hF.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  obtain ⟨Q, hQne, hQdeg, hQheight, hQzero⟩ := BoundedPlaneInterpolation.exists_bounded_equation
    (PlaneCurvePointCount.degree F) B hB F hne le_rfl S hbox hzero
  have hinj : Function.Injective (IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ)) :=
    IntegerCurveRationalization.coefficientMap_injective _ Int.cast_injective
  have hRQ : rationalize Q ≠ 0 := by
    intro hz
    apply hQne
    apply hinj
    exact hz.trans (map_zero _).symm
  have hdF : PlaneCurvePointCount.degree (rationalize F) = PlaneCurvePointCount.degree F :=
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective F
  have hdQ : PlaneCurvePointCount.degree (rationalize Q) = PlaneCurvePointCount.degree Q :=
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective Q
  have hdiv : rationalize F ∣ rationalize Q := by
    by_contra hn
    let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
    have hi : Function.Injective f := by
      intro z w he
      exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
        (Int.cast_injective (congrArg Prod.snd he))
    have hc := FinitePlaneBezout.common_points_card (rationalize F) (rationalize Q) hF hn (S.image f) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      constructor
      · rw [rationalized_evaluation, hzero w hw, Int.cast_zero]
      · rw [rationalized_evaluation, hQzero w hw, Int.cast_zero])
    rw [card_image_of_injective _ hi, hdF, hdQ] at hc
    have hb := hc.trans (Nat.mul_le_mul_left (PlaneCurvePointCount.degree F) hQdeg)
    rw [← pow_two] at hb
    omega
  obtain ⟨hassoc, hdeg⟩ := ManyPointsScalarDescent.divisor_associated (rationalize F) (rationalize Q)
    hF.ne_zero hRQ (by rw [hdF, hdQ]; exact hQdeg) hdiv
  rw [hdF, hdQ] at hdeg
  have hQgeo : Irreducible (extend (rationalize Q) : ℂ[X][X]) := by
    let φ := Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    exact (Associated.map φ hassoc).irreducible hgeo
  exact ⟨Q, hassoc.irreducible hF, hQgeo, hassoc, hdeg, hQheight, hQzero⟩

end PaperP1.SmallHeightAssociatedPlanePresentation
