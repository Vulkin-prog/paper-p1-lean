module

public import PaperP1.Arithmetic.IntegralGeometricPlanePointInput
public import PaperP1.Arithmetic.BoundedPlaneInterpolation

/-! # The remaining plane count only needs controlled coefficient height

This is a checked restriction of the ordinary unproved geometric plane count.
The actual counting estimate at controlled coefficient height is not asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallHeightGeometricPlanePointInput

open Polynomial Finset PaperP1.PolynomialScalarProjection PaperP1.CurveDegreeProfile
open PaperP1.RationalBivariateIrreducibility

theorem rationalized_evaluation (F : ℤ[X][X]) (z : ℤ × ℤ) :
    (rationalize F).evalEval (z.1 : ℚ) (z.2 : ℚ) = ((F.evalEval z.1 z.2 : ℤ) : ℚ) :=
  Polynomial.map_mapRingHom_evalEval (Int.castRingHom ℚ) F z.1 z.2

theorem exists_small_presentation (F : ℤ[X][X]) (hF : Irreducible (rationalize F))
    (hgeo : Irreducible (extend (rationalize F) : ℂ[X][X])) (B : ℕ) (hB : 1 ≤ B)
    (S : Finset (ℤ × ℤ)) (hbox : ∀ z ∈ S, z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B)
    (hzero : ∀ z ∈ S, F.evalEval z.1 z.2 = 0)
    (hmany : PlaneCurvePointCount.degree F ^ 2 < S.card) :
    ∃ Q : ℤ[X][X], Irreducible (rationalize Q) ∧
      Irreducible (extend (rationalize Q) : ℂ[X][X]) ∧
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
  exact ⟨Q, hassoc.irreducible hF, hQgeo, hdeg, hQheight, hQzero⟩

def Input (c κ : ℝ) : Prop :=
  ∀ F : ℤ[X][X], Irreducible (rationalize F) → Irreducible (extend (rationalize F) : ℂ[X][X]) →
    2 ≤ PlaneCurvePointCount.degree F → ∀ H : ℝ, 2 < H →
      BivariateHeight.height F ≤ BoundedPlaneInterpolation.heightBound (PlaneCurvePointCount.degree F) ⌊H⌋₊ →
      ((PlaneCurvePointCount.grid F ⌊H⌋₊).card : ℝ) ≤
        c * profile H (PlaneCurvePointCount.degree F : ℝ) * Real.log H ^ κ

theorem integral_input (c κ : ℝ) (hκ : 0 ≤ κ) (hSmall : Input c κ) :
    IntegralGeometricPlanePointInput.Input (GeometricPlanePointInput.constant c κ) κ := by
  intro F hF hgeo hD H hH
  classical
  let B := ⌊H⌋₊
  let S := PlaneCurvePointCount.grid F B
  by_cases hsmall : S.card ≤ PlaneCurvePointCount.degree F ^ 2
  · have hc : (S.card : ℝ) ≤ (PlaneCurvePointCount.degree F : ℝ) ^ 2 := by exact_mod_cast hsmall
    exact hc.trans (RationalGeometricPlanePointInput.degree_square_budget c κ H hκ hH _)
  have hB : 1 ≤ B := (Nat.one_le_floor_iff H).mpr (by linarith)
  have hbox (z : ℤ × ℤ) (hz : z ∈ S) : z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B := by
    have hh := (PlaneCurvePointCount.mem_grid F B z).mp hz
    constructor
    · have hc : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
      exact_mod_cast hc
    · have hc : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
      exact_mod_cast hc
  obtain ⟨Q, hQ, hQgeo, hdeg, hheight, hzero⟩ := exists_small_presentation F hF hgeo B hB S hbox
    (fun z hz ↦ ((PlaneCurvePointCount.mem_grid F B z).mp hz).2.2) (by omega)
  have hsub : S ⊆ PlaneCurvePointCount.grid Q B := by
    intro z hz
    have hh := (PlaneCurvePointCount.mem_grid F B z).mp hz
    exact (PlaneCurvePointCount.mem_grid Q B z).mpr ⟨hh.1, hh.2.1, hzero z hz⟩
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hb := hSmall Q hQ hQgeo (by omega) H hH (by simpa only [hdeg] using hheight)
  rw [hdeg] at hb
  have hp : 0 ≤ profile H (PlaneCurvePointCount.degree F : ℝ) := by unfold profile; positivity
  have hl : 0 ≤ Real.log H ^ κ := Real.rpow_nonneg (Real.log_nonneg (by linarith)) κ
  have hconstant : c ≤ GeometricPlanePointInput.constant c κ := le_max_left _ _
  exact hc.trans (hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hp) hl))

theorem field_input (c κ : ℝ) (hκ : 0 ≤ κ) (hSmall : Input c κ) :
    PlaneCurvePointCount.UniformBound (GeometricPlanePointInput.constant c κ) κ := by
  have hh := IntegralGeometricPlanePointInput.field_input _ κ hκ (integral_input c κ hκ hSmall)
  simpa only [GeometricPlanePointInput.constant, max_assoc, max_self] using hh

theorem integer_input (c κ : ℝ) (hκ : 0 ≤ κ) (hSmall : Input c κ) :
    IntegerCurvePointInput.UniformBound (GeometricPlanePointInput.constant c κ) κ :=
  IntegerCurveRationalization.integer_input_of_field_input _ _ (field_input c κ hκ hSmall)

theorem restriction_of_integral_input (c κ : ℝ) (hInt : IntegralGeometricPlanePointInput.Input c κ) :
    Input c κ := by
  intro F hF hgeo hD H hH _hheight
  exact hInt F hF hgeo hD H hH

end PaperP1.SmallHeightGeometricPlanePointInput
