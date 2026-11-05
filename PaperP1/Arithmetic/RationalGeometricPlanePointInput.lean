module

public import PaperP1.Algebra.ManyPointsScalarDescent
public import PaperP1.Arithmetic.GeometricPlanePointInput

/-! # Only the rational geometric plane estimate remains as an ordinary BCN input

The rational estimate is not proved here. Arbitrary coefficient fields, small
populations, linear equations and non-geometric equations are reduced internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGeometricPlanePointInput

open Polynomial Finset PaperP1.PolynomialScalarProjection PaperP1.CurveDegreeProfile

def Input (c κ : ℝ) : Prop :=
  ∀ P : ℚ[X][X], Irreducible P → Irreducible (extend P : ℂ[X][X]) →
    2 ≤ PlaneCurvePointCount.degree P → ∀ H : ℝ, 2 < H →
      ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
        c * profile H (PlaneCurvePointCount.degree P : ℝ) * Real.log H ^ κ

theorem extend_tower {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (P : K[X][X]) :
    (extend (extend P : L[X][X]) : M[X][X]) = (extend P : M[X][X]) := by
  ext i j
  rw [extend_coefficient, extend_coefficient, extend_coefficient,
    ← IsScalarTower.algebraMap_apply K L M]

theorem absolute_of_associated_extension (K : Type) [Field K] [CharZero K] [Algebra K ℂ]
    (P : K[X][X]) (Q : ℚ[X][X]) (hassoc : Associated P (extend Q : K[X][X]))
    (hP : Irreducible (extend P : ℂ[X][X])) : Irreducible (extend Q : ℂ[X][X]) := by
  let φ := Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap K ℂ))
  have hh := Associated.map φ hassoc
  change Associated (extend P : ℂ[X][X]) (extend (extend Q : K[X][X]) : ℂ[X][X]) at hh
  rw [extend_tower] at hh
  exact hh.irreducible hP

theorem degree_square_budget (c κ H : ℝ) (hκ : 0 ≤ κ) (hH : 2 < H) (D : ℕ) :
    (D : ℝ) ^ 2 ≤ GeometricPlanePointInput.constant c κ * profile H (D : ℝ) * Real.log H ^ κ := by
  have hp : (D : ℝ) ^ 2 ≤ profile H (D : ℝ) := by
    unfold profile
    exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_rpow (by linarith)
      (one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have hprof : 0 ≤ profile H (D : ℝ) := by unfold profile; positivity
  have hn : 1 ≤ GeometricPlanePointInput.constant c κ * Real.log H ^ κ :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (GeometricPlanePointInput.logarithmic_budget c κ H hκ hH)
  calc
    _ ≤ profile H (D : ℝ) := hp
    _ ≤ profile H (D : ℝ) * (GeometricPlanePointInput.constant c κ * Real.log H ^ κ) :=
      le_mul_of_one_le_right hprof hn
    _ = _ := by ring

theorem geometric_input (c κ : ℝ) (hκ : 0 ≤ κ) (hRat : Input c κ) :
    GeometricPlanePointInput.Input (GeometricPlanePointInput.constant c κ) κ := by
  intro K _hK _hchar _halg P hP hgeom hD H hH
  classical
  let T := PlaneCurvePointCount.grid P ⌊H⌋₊
  by_cases hsmall : T.card ≤ PlaneCurvePointCount.degree P ^ 2
  · have hc : (T.card : ℝ) ≤ (PlaneCurvePointCount.degree P : ℝ) ^ 2 := by exact_mod_cast hsmall
    exact hc.trans (degree_square_budget c κ H hκ hH _)
  let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
  have hi : Function.Injective f := by
    intro z w he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hpoints : ∀ z ∈ T.image f, P.evalEval (algebraMap ℚ K z.1) (algebraMap ℚ K z.2) = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := ((PlaneCurvePointCount.mem_grid P ⌊H⌋₊ w).mp hw).2.2
    simpa only [f, map_intCast] using hh
  obtain ⟨Q, hQ, hassoc, hdeg, hzero⟩ := ManyPointsScalarDescent.many_points_descent P hP (T.image f)
    hpoints (by rw [card_image_of_injective _ hi]; omega)
  have hQgeo := absolute_of_associated_extension K P Q hassoc hgeom
  have hsub : T ⊆ PlaneCurvePointCount.grid Q ⌊H⌋₊ := by
    intro z hz
    have hb := (PlaneCurvePointCount.mem_grid P ⌊H⌋₊ z).mp hz
    apply (PlaneCurvePointCount.mem_grid Q ⌊H⌋₊ z).mpr
    exact ⟨hb.1, hb.2.1, hzero (f z) (mem_image.mpr ⟨z, hz, rfl⟩)⟩
  have hc : (T.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q ⌊H⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hb := hRat Q hQ hQgeo (by omega) H hH
  rw [hdeg] at hb
  have hprofile : 0 ≤ profile H (PlaneCurvePointCount.degree P : ℝ) := by unfold profile; positivity
  have hlog : 0 ≤ Real.log H ^ κ := Real.rpow_nonneg (Real.log_nonneg (by linarith)) κ
  have hconstant : c ≤ GeometricPlanePointInput.constant c κ := le_max_left _ _
  exact hc.trans (hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconstant hprofile) hlog))

theorem field_input (c κ : ℝ) (hκ : 0 ≤ κ) (hRat : Input c κ) :
    PlaneCurvePointCount.UniformBound (GeometricPlanePointInput.constant c κ) κ := by
  have hh := GeometricPlanePointInput.field_input _ κ hκ (geometric_input c κ hκ hRat)
  simpa only [GeometricPlanePointInput.constant, max_assoc, max_self] using hh

theorem integer_input (c κ : ℝ) (hκ : 0 ≤ κ) (hRat : Input c κ) :
    IntegerCurvePointInput.UniformBound (GeometricPlanePointInput.constant c κ) κ :=
  IntegerCurveRationalization.integer_input_of_field_input _ _ (field_input c κ hκ hRat)

theorem restriction_of_geometric_input (c κ : ℝ) (hGeo : GeometricPlanePointInput.Input c κ) :
    Input c κ := by
  intro P hP hgeom hD H hH
  exact hGeo ℚ P hP hgeom hD H hH

end PaperP1.RationalGeometricPlanePointInput
