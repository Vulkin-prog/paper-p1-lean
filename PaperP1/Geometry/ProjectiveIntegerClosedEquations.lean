module

public import PaperP1.Algebra.FiniteHomogeneousIdealBasis
public import PaperP1.Geometry.P3FactorMultiplicationProper
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Actual finite homogeneous integer equations for the proved closed projective factor images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveIntegerClosedEquations

open AlgebraicGeometry MvPolynomial P3HomogeneousCoefficientFamily
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finite_equations {σ : Type} [Finite σ]
    (Y : Set (ProjectiveSpectrum (homogeneousSubmodule σ ℤ))) (hY : IsClosed Y) :
    ∃ forms : Finset (MvPolynomial σ ℤ),
      (∀ P ∈ forms, ∃ n : ℕ, P.IsHomogeneous n) ∧
      ∀ p : ProjectiveSpectrum (homogeneousSubmodule σ ℤ),
        p ∈ Y ↔ ∀ P ∈ forms, P ∈ p.asHomogeneousIdeal := by
  let G := homogeneousSubmodule σ ℤ
  let I := ProjectiveSpectrum.vanishingIdeal (𝒜 := G) Y
  obtain ⟨forms, hhom, hspan⟩ := FiniteHomogeneousIdealBasis.exists_generators I.toIdeal I.isHomogeneous
  have he : ProjectiveSpectrum.zeroLocus G (forms : Set (MvPolynomial σ ℤ)) = Y := by
    rw [← ProjectiveSpectrum.zeroLocus_span, hspan]
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure G Y).trans hY.closure_eq
  refine ⟨forms, hhom, ?_⟩
  intro p
  rw [← he]
  rfl

theorem factor_image_equations (e f : ℕ) :
    ∃ forms : Finset (MvPolynomial (Index (e + f)) ℤ),
      (∀ P ∈ forms, ∃ n : ℕ, P.IsHomogeneous n) ∧
      ∀ p : ProjectiveSpectrum (homogeneousSubmodule (Index (e + f)) ℤ),
        p ∈ Set.range (P3FactorMultiplicationMap.multiplication e f) ↔
          ∀ P ∈ forms, P ∈ p.asHomogeneousIdeal :=
  finite_equations _ (P3FactorMultiplicationProper.image_closed e f)

end PaperP1.ProjectiveIntegerClosedEquations
