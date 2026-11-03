module

public import PaperP1.Geometry.OrdinaryCurveSourceHeight
public import PaperP1.Algebra.GradedHilbertPolynomial

/-! # Actual ordinary surface curves with their prime ideals and actual linear Hilbert polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySurfaceCurveData

open Polynomial PaperP1.HomogeneousSplitRadicalRelations PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

structure Curve {ι : Type*} (c : ι → ℚ) (D : ℕ) (I J : ι → Finset ℤ) where
  ideal : Ideal (WeightedPolynomial ℚ ι)
  prime : ideal.IsPrime
  homogeneous : ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3 ⊕ ι) ℚ)
  relations : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ ideal
  height : (OrdinaryCurveSourceHeight.surfaceIdeal c D I J ideal relations).height = 1
  degree : ℕ
  degree_pos : 0 < degree
  constant : ℚ
  hilbert : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece ideal) (C (degree : ℚ) * X + C constant)

variable {ι : Type*} {c : ι → ℚ} {D : ℕ} {I J : ι → Finset ℤ}

theorem degree_unique (Γ Δ : Curve c D I J) (h : Γ.ideal = Δ.ideal) : Γ.degree = Δ.degree := by
  have hp := GradedHilbertPolynomial.unique Γ.hilbert (h.symm ▸ Δ.hilbert)
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hp
  have heq : (Γ.degree : ℚ) = (Δ.degree : ℚ) := by simpa using hc
  exact_mod_cast heq

end PaperP1.OrdinarySurfaceCurveData
