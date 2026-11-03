module

public import PaperP1.Algebra.HomogeneousPieceBasis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The literal monomial basis of every homogeneous polynomial piece -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MvPolynomialHomogeneousBasis

open Module

attribute [local instance] MvPolynomial.gradedAlgebra

theorem monomial_homogeneous (F σ : Type*) [CommRing F] (d : σ →₀ ℕ) :
    MvPolynomial.basisMonomials σ F d ∈ MvPolynomial.homogeneousSubmodule σ F d.degree := by
  change (MvPolynomial.monomial d (1 : F)).IsHomogeneous d.degree
  exact MvPolynomial.isHomogeneous_monomial 1 rfl

def pieceBasis (F σ : Type*) [CommRing F] (n : ℕ) :
    Basis {d : σ →₀ ℕ // d.degree = n} F (MvPolynomial.homogeneousSubmodule σ F n) :=
  HomogeneousPieceBasis.pieceBasis (MvPolynomial.homogeneousSubmodule σ F)
    (MvPolynomial.basisMonomials σ F) Finsupp.degree (monomial_homogeneous F σ) n

theorem pieceBasis_apply (F σ : Type*) [CommRing F] (n : ℕ) (d : {d : σ →₀ ℕ // d.degree = n}) :
    (pieceBasis F σ n d : MvPolynomial σ F) = MvPolynomial.monomial d.1 1 := by
  rw [pieceBasis, HomogeneousPieceBasis.pieceBasis_apply]
  rfl

end PaperP1.MvPolynomialHomogeneousBasis
