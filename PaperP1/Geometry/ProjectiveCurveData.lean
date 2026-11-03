module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Actual homogeneous prime curve ideals with their linear Hilbert polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveCurveData

open Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

def piece {σ : Type} (Q : Ideal (MvPolynomial σ ℚ)) (n : ℕ) : Submodule ℚ ((MvPolynomial σ ℚ) ⧸ Q) :=
  HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ ℚ) Q n

structure Curve (σ : Type) where
  ideal : Ideal (MvPolynomial σ ℚ)
  prime : ideal.IsPrime
  homogeneous : ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℚ)
  degree : ℚ
  degree_pos : 0 < degree
  constant : ℚ
  hilbert : GradedHilbertPolynomial.IsHilbertPolynomial (piece ideal) (C degree * X + C constant)

theorem degree_unique {σ : Type} (Γ Δ : Curve σ) (h : Γ.ideal = Δ.ideal) : Γ.degree = Δ.degree := by
  have hp := GradedHilbertPolynomial.unique Γ.hilbert (h.symm ▸ Δ.hilbert)
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hp
  simpa using hc

end PaperP1.ProjectiveCurveData
