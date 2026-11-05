module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Actual scalar multiplication preserves the zeros of a homogeneous ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousIdealPointScaling

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zeros_scale {F σ : Type*} [CommRing F] (I : Ideal (MvPolynomial σ F))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) (w : σ → F)
    (hw : ∀ P ∈ I, eval w P = 0) (c : F) :
    ∀ P ∈ I, eval (fun i ↦ c * w i) P = 0 := by
  classical
  intro P hP
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro n _hn
  rw [HomogeneousPolynomialEvaluation.eval_scale _ (homogeneousComponent_mem n P)]
  rw [hw _ ((mem_iff_homogeneousComponent_mem hI P).mp hP n), mul_zero]

end PaperP1.HomogeneousIdealPointScaling
