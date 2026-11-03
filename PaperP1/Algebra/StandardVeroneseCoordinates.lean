module

public import PaperP1.Algebra.SourceVeroneseGrading
public import PaperP1.Algebra.HomogeneousSplitRadicalVeroneseTowerData

/-! # The literal coordinate powers in the native standard Veronese base -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardVeroneseCoordinates

open PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

def coordinatePower (F : Type*) [Field F] (D : ℕ) (j : Fin 3) : Base F D :=
  ⟨MvPolynomial.X j ^ D, GradedVeroneseAlgebra.piece_mem
    (MvPolynomial.homogeneousSubmodule (Fin 3) F) D 1 (by
      change (MvPolynomial.X j ^ D : MvPolynomial (Fin 3) F).IsHomogeneous (1 * D)
      simpa only [one_mul, mul_one] using (MvPolynomial.isHomogeneous_X F j).pow D)⟩

theorem coordinatePower_val (F : Type*) [Field F] (D : ℕ) (j : Fin 3) :
    (coordinatePower F D j : MvPolynomial (Fin 3) F) = MvPolynomial.X j ^ D := rfl

theorem coordinatePower_mem (F : Type*) [Field F] (D : ℕ) (j : Fin 3) :
    coordinatePower F D j ∈ nativePiece F D 1 := by
  change (MvPolynomial.X j ^ D : MvPolynomial (Fin 3) F).IsHomogeneous (1 * D)
  simpa only [one_mul, mul_one] using (MvPolynomial.isHomogeneous_X F j).pow D

theorem coordinatePower_ne_zero (F : Type*) [Field F] (D : ℕ) (j : Fin 3) :
    coordinatePower F D j ≠ 0 := by
  intro hzero
  have h := congrArg (fun p : Base F D ↦ (p : MvPolynomial (Fin 3) F)) hzero
  exact (pow_ne_zero D (MvPolynomial.X_ne_zero j)) h

end PaperP1.StandardVeroneseCoordinates
