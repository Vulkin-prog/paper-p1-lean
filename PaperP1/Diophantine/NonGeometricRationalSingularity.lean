module

public import PaperP1.Diophantine.PrimitiveRationalPointLift
public import PaperP1.Diophantine.NonGeometricBiformInput
public import PaperP1.Arithmetic.IntegerPairFactorCharts

/-! # The non-geometric count follows from an explicit algebraic singularity premise

`Input` is now proved by ComplexProjectiveIrreducibility.singularity_input.
The implication and numerical reduction are preserved as explicit APIs; no
unproved singularity argument is needed. The complete numerical input follows
with constant 8*a*b^2. See P1-MATH-0330 for the exact projective identification.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonGeometricRationalSingularity

open Polynomial PaperP1.BivariateDegrees PaperP1.RationalBivariateIrreducibility
  PaperP1.GeometricFactorSwap PaperP1.PrimitiveDirections

def Input : Prop :=
  ∀ G : ℤ[X][X], 0 < degreeX G → 0 < degreeY G →
    Irreducible (rationalize G) → ¬Geometric G → ∀ x y : ℚ,
      (rationalize G).evalEval x y = 0 → (rationalize G).derivative.evalEval x y = 0

theorem rationalize_evaluation (G : ℤ[X][X]) (x y : ℚ) :
    (rationalize G).evalEval x y = PaperP1.BivariateEvaluation.evaluate x y G := by
  have he : (Polynomial.evalEvalRingHom x y).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
        PaperP1.BivariateEvaluation.evaluate x y := by
    ext <;> simp [PaperP1.BivariateEvaluation.evaluate]
  exact congrArg (fun f : ℤ[X][X] →+* ℚ ↦ f G) he

theorem projective_zero_iff (G : ℤ[X][X]) (x y : Fin 2 → ℤ)
    (hx : x 1 ≠ 0) (hy : y 1 ≠ 0) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x
      (PaperP1.IntegerFactorProjectiveCurve.projective G) = 0 ↔
        (rationalize G).evalEval (ratio x) (ratio y) = 0 := by
  rw [rationalize_evaluation]
  exact PaperP1.IntegerPairFactorCharts.projective_zero_iff G x y hx hy

theorem nongeometric_input_of_singularity (hSing : Input) :
    PaperP1.NonGeometricBiformInput.Input := by
  intro a b ha hb
  refine ⟨((8 * a * b ^ 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro G hX hY hG hgeom S hprimitive hden hzero
  have hposX : 0 < degreeX G := hX ▸ ha
  have hposY : 0 < degreeY G := hY ▸ hb
  have hc := PaperP1.PrimitiveRationalPointLift.primitive_critical_points_card
    G hG hposY S hprimitive hden (by
      intro s hs
      have hz := (projective_zero_iff G s.1 s.2 (hden s hs).1 (hden s hs).2).mp
        (hzero s hs)
      exact ⟨hz, hSing G hposX hposY hG hgeom (ratio s.1) (ratio s.2) hz⟩)
  rw [hX, hY] at hc
  exact_mod_cast hc

end PaperP1.NonGeometricRationalSingularity
