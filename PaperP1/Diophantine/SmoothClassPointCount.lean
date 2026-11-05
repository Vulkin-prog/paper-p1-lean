module

public import PaperP1.Diophantine.SmoothClassAuxiliary
public import PaperP1.Diophantine.PrimitiveRationalPointLift
public import PaperP1.Algebra.ScalarIrreducibilityReflection
public import PaperP1.Algebra.FinitePlaneBezout
public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Arithmetic.IntegerCurveRationalization

/-! # A degree-uniform count for each actual smooth projective residue class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothClassPointCount

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.RationalBivariateIrreducibility
open PaperP1.PrimitiveRationalPointLift

theorem rationalize_ne_zero (F : ℤ[X][X]) (hF : F ≠ 0) : rationalize F ≠ 0 := by
  have hi : Function.Injective (IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ)) :=
    IntegerCurveRationalization.coefficientMap_injective _ Int.cast_injective
  intro hz
  apply hF
  apply hi
  exact hz.trans (map_zero _).symm

theorem degree_rationalize (F : ℤ[X][X]) :
    PlaneCurvePointCount.degree (rationalize F) ≤ degreeX F + degreeY F := by
  rw [show rationalize F = IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ) F from rfl,
    IntegerCurveRationalization.degree_coefficientMap _ Int.cast_injective]
  exact BivariateCurveDegreeTransport.degree_le_partial_sum F

theorem common_points_card (G F : ℤ[X][X]) (hG : Irreducible (rationalize G))
    (hF : F ≠ 0) (hdegree : degreeY F < degreeY G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hden : ∀ z ∈ S, z.1 1 ≠ 0 ∧ z.2 1 ≠ 0)
    (hz : ∀ z ∈ S,
      BivariateEvaluation.evaluate ((z.1 0 : ℚ) / z.1 1) ((z.2 0 : ℚ) / z.2 1) G = 0 ∧
      BivariateEvaluation.evaluate ((z.1 0 : ℚ) / z.1 1) ((z.2 0 : ℚ) / z.2 1) F = 0) :
    S.card ≤ 4 * (degreeX G + degreeY G) * (degreeX F + degreeY F) := by
  classical
  have hnot : ¬rationalize G ∣ rationalize F := by
    intro hd
    have he := Polynomial.natDegree_le_of_dvd hd (rationalize_ne_zero F hF)
    rw [RationalizedCriticalPointBound.outer_degree, RationalizedCriticalPointBound.outer_degree] at he
    omega
  have hc := FinitePlaneBezout.common_points_card (rationalize G) (rationalize F) hG hnot
    (S.image affine) (by
      intro r hr
      obtain ⟨z, hzS, rfl⟩ := mem_image.mp hr
      simpa only [affine, PrimitiveDirections.ratio, rationalize,
        ProjectiveSmoothDeterminant.coefficient_evaluation] using hz z hzS)
  calc
    S.card ≤ 4 * (S.image affine).card := card_le_four_image S hprim hden
    _ ≤ 4 * (PlaneCurvePointCount.degree (rationalize G) *
        PlaneCurvePointCount.degree (rationalize F)) := Nat.mul_le_mul_left _ hc
    _ ≤ 4 * ((degreeX G + degreeY G) * (degreeX F + degreeY F)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (degree_rationalize G) (degree_rationalize F))
    _ = _ := by ring

theorem smooth_class_card (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (hJ : J < degreeY G) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hclass : ∀ z ∈ S, SmoothClassAuxiliary.ClassPoint p G a b z)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y)
    (hsmall : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2)) :
    S.card ≤ 4 * (degreeX G + degreeY G) * (H + J) := by
  have hden (z : Point) (hzS : z ∈ S) : z.1 1 ≠ 0 ∧ z.2 1 ≠ 0 := by
    constructor
    · intro h
      exact (hclass z hzS).denominatorX (by rw [h]; exact dvd_zero _)
    · intro h
      exact (hclass z hzS).denominatorY (by rw [h]; exact dvd_zero _)
  obtain ⟨F, hF, hFX, hFY, hzero⟩ := SmoothClassAuxiliary.exists_auxiliary p hp G a b hG hder
    H J L Y hL hY S hclass hx hy hsmall
  have hc := common_points_card G F
    (ScalarIrreducibilityReflection.geometric_rational_irreducible G hne hgeom)
    hF (hFY.trans_lt hJ) S hprim hden (by
      intro z hzS
      exact ⟨(IntegerPairFactorCharts.projective_zero_iff G z.1 z.2
        (hden z hzS).1 (hden z hzS).2).mp (hclass z hzS).equation, (hzero z hzS).1⟩)
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.add_le_add hFX hFY))

end PaperP1.SmoothClassPointCount
