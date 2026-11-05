module

public import PaperP1.Arithmetic.SmallHeightAssociatedPlanePresentation

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
  obtain ⟨Q, hQ, hQgeo, _hassoc, hdeg, hheight, hzero⟩ :=
    SmallHeightAssociatedPlanePresentation.exists_presentation F hF hgeo B hB S hbox hzero hmany
  exact ⟨Q, hQ, hQgeo, hdeg, hheight, hzero⟩

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
