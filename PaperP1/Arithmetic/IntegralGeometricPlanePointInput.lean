module

public import PaperP1.Arithmetic.RationalGeometricPlanePointInput

/-! # Clearing denominators reduces the remaining plane estimate to integer equations

The geometric integer plane count remains an explicit unproved property.
Clearing denominators preserves the actual grids and exact total degree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralGeometricPlanePointInput

open Polynomial Finset PaperP1.PolynomialScalarProjection PaperP1.CurveDegreeProfile
open PaperP1.RationalBivariateIrreducibility

attribute [local instance] Polynomial.algebra

theorem exists_integral_presentation (Q : ℚ[X][X]) :
    ∃ F : ℤ[X][X], ∃ n : ℤ, n ≠ 0 ∧ rationalize F = C (C (n : ℚ)) * Q := by
  let S : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map Polynomial.C
  let : IsLocalization S ℚ[X] := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  let : IsLocalization (S.map Polynomial.C) ℚ[X][X] := Polynomial.isLocalization S ℚ[X]
  obtain ⟨⟨F, s⟩, hs⟩ := IsLocalization.surj (S.map Polynomial.C) Q
  obtain ⟨t, ht, hts⟩ := Submonoid.mem_map.mp s.property
  obtain ⟨n, hn, hnt⟩ := Submonoid.mem_map.mp ht
  have hn0 : n ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
  have hform : (s : ℤ[X][X]) = C (C n) := by rw [← hts, ← hnt]
  change Q * rationalize (s : ℤ[X][X]) = rationalize F at hs
  rw [hform] at hs
  have he : Q * C (C (n : ℚ)) = rationalize F := by
    simpa only [rationalize, Polynomial.coe_mapRingHom, Polynomial.map_C, Int.coe_castRingHom] using hs
  exact ⟨F, n, hn0, he.symm.trans (mul_comm _ _)⟩

theorem presentation_properties (Q : ℚ[X][X]) (hQ : Irreducible Q)
    (hgeo : Irreducible (extend Q : ℂ[X][X])) (F : ℤ[X][X]) (n : ℤ) (hn : n ≠ 0)
    (hF : rationalize F = C (C (n : ℚ)) * Q) :
    Irreducible (rationalize F) ∧ Irreducible (extend (rationalize F) : ℂ[X][X]) ∧
      PlaneCurvePointCount.degree F = PlaneCurvePointCount.degree Q ∧
        ∀ B : ℕ, PlaneCurvePointCount.grid F B = PlaneCurvePointCount.grid Q B := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hu : IsUnit (C (C (n : ℚ)) : ℚ[X][X]) :=
    Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hnQ))
  have hassoc : Associated Q (rationalize F) := by
    rw [hF]
    exact associated_unit_mul_right Q _ hu
  have hgeoF : Irreducible (extend (rationalize F) : ℂ[X][X]) := by
    let φ := Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    exact (Associated.map φ hassoc).irreducible hgeo
  have hd := ManyPointsScalarDescent.degree_mul (C (C (n : ℚ))) Q hu.ne_zero hQ.ne_zero
  rw [← hF, IntegerCurveRationalization.degree_of_isUnit _ hu, zero_add] at hd
  have hmap : PlaneCurvePointCount.degree (rationalize F) = PlaneCurvePointCount.degree F :=
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective F
  refine ⟨hassoc.irreducible hQ, hgeoF, hmap.symm.trans hd, ?_⟩
  intro B
  have hgrid : PlaneCurvePointCount.grid (rationalize F) B = PlaneCurvePointCount.grid F B :=
    IntegerCurveRationalization.grid_coefficientMap _ Int.cast_injective F B
  rw [← hgrid]
  ext z
  simp only [PlaneCurvePointCount.mem_grid, hF, Polynomial.evalEval_mul, Polynomial.evalEval_CC,
    mul_eq_zero, hnQ, false_or]

def Input (c κ : ℝ) : Prop :=
  ∀ F : ℤ[X][X], Irreducible (rationalize F) → Irreducible (extend (rationalize F) : ℂ[X][X]) →
    2 ≤ PlaneCurvePointCount.degree F → ∀ H : ℝ, 2 < H →
      ((PlaneCurvePointCount.grid F ⌊H⌋₊).card : ℝ) ≤
        c * profile H (PlaneCurvePointCount.degree F : ℝ) * Real.log H ^ κ

theorem rational_input (c κ : ℝ) (hInt : Input c κ) : RationalGeometricPlanePointInput.Input c κ := by
  intro Q hQ hgeo hD H hH
  obtain ⟨F, n, hn, hF⟩ := exists_integral_presentation Q
  obtain ⟨hRF, hgeoF, hdeg, hgrid⟩ := presentation_properties Q hQ hgeo F n hn hF
  have hb := hInt F hRF hgeoF (by omega) H hH
  rw [hdeg, hgrid] at hb
  exact hb

theorem field_input (c κ : ℝ) (hκ : 0 ≤ κ) (hInt : Input c κ) :
    PlaneCurvePointCount.UniformBound (GeometricPlanePointInput.constant c κ) κ :=
  RationalGeometricPlanePointInput.field_input c κ hκ (rational_input c κ hInt)

theorem integer_input (c κ : ℝ) (hκ : 0 ≤ κ) (hInt : Input c κ) :
    IntegerCurvePointInput.UniformBound (GeometricPlanePointInput.constant c κ) κ :=
  IntegerCurveRationalization.integer_input_of_field_input _ _ (field_input c κ hκ hInt)

theorem restriction_of_rational_input (c κ : ℝ) (hRat : RationalGeometricPlanePointInput.Input c κ) :
    Input c κ := by
  intro F hF hgeo hD H hH
  have hd : PlaneCurvePointCount.degree (rationalize F) = PlaneCurvePointCount.degree F :=
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective F
  have hg : PlaneCurvePointCount.grid (rationalize F) ⌊H⌋₊ = PlaneCurvePointCount.grid F ⌊H⌋₊ :=
    IntegerCurveRationalization.grid_coefficientMap _ Int.cast_injective F _
  have hb := hRat (rationalize F) hF hgeo (by omega) H hH
  simpa only [hd, hg] using hb

end PaperP1.IntegralGeometricPlanePointInput
