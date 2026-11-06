module

public import PaperP1.Geometry.ProjectiveCurveData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.Ideal.Height

/-! # Actual height-one projective primes with their genuine quotient Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedProjectiveCurveData

open Polynomial

structure Curve {F B : Type*} [Field F] [CommRing B] [Algebra F B]
    (H : ℕ → Submodule F B) [GradedAlgebra H] where
  point : ProjectiveSpectrum H
  height : point.asHomogeneousIdeal.toIdeal.height = 1
  degree : ℚ
  degree_pos : 0 < degree
  constant : ℚ
  hilbert : GradedHilbertPolynomial.IsHilbertPolynomial
    (HomogeneousQuotientGrading.piece H point.asHomogeneousIdeal.toIdeal)
    (C degree * X + C constant)

variable {F B : Type*} [Field F] [CommRing B] [Algebra F B]
  {H : ℕ → Submodule F B} [GradedAlgebra H]

def Curve.ideal (Γ : Curve H) : Ideal B := Γ.point.asHomogeneousIdeal.toIdeal

theorem Curve.ideal_prime (Γ : Curve H) : Γ.ideal.IsPrime := Γ.point.isPrime

theorem Curve.ideal_homogeneous (Γ : Curve H) : Γ.ideal.IsHomogeneous H := Γ.point.asHomogeneousIdeal.isHomogeneous

theorem Curve.ideal_height (Γ : Curve H) : Γ.ideal.height = 1 := Γ.height

theorem Curve.ideal_hilbert (Γ : Curve H) : GradedHilbertPolynomial.IsHilbertPolynomial
    (HomogeneousQuotientGrading.piece H Γ.ideal) (C Γ.degree * X + C Γ.constant) := Γ.hilbert

theorem Curve.degree_unique (Γ Δ : Curve H) (he : Γ.ideal = Δ.ideal) : Γ.degree = Δ.degree := by
  have hΔ := Δ.ideal_hilbert
  rw [← he] at hΔ
  have hp := GradedHilbertPolynomial.unique Γ.ideal_hilbert hΔ
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hp
  simpa using hc

end PaperP1.GradedProjectiveCurveData
