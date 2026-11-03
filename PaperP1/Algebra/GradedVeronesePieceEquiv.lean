module

public import PaperP1.Algebra.GradedVeroneseGrading
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The actual rescaled Veronese pieces are the original pieces in degrees nD -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeronesePieceEquiv

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
variable (G : ℕ → Submodule F A) [GradedAlgebra G] (D n : ℕ)

def equiv : GradedVeroneseGrading.piece G D n ≃ₗ[F] G (n * D) where
  toFun x := ⟨((x : GradedVeroneseAlgebra.veronese G D) : A), x.property⟩
  invFun p := ⟨⟨p, GradedVeroneseAlgebra.piece_mem G D n p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem equiv_val (x : GradedVeroneseGrading.piece G D n) :
    (equiv G D n x : A) = ((x : GradedVeroneseAlgebra.veronese G D) : A) := rfl

theorem finrank_eq : Module.finrank F (GradedVeroneseGrading.piece G D n) =
    Module.finrank F (G (n * D)) := (equiv G D n).finrank_eq

theorem finite [Module.Finite F (G (n * D))] :
    Module.Finite F (GradedVeroneseGrading.piece G D n) :=
  Module.Finite.of_surjective (equiv G D n).symm.toLinearMap (equiv G D n).symm.surjective

end PaperP1.GradedVeronesePieceEquiv
