module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Actual irreducibility over an algebraically closed field equals the canonical geometric criterion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlgClosedPolynomialIrreducibility

open MvPolynomial

def closureEquiv (F : Type*) [Field F] [IsAlgClosed F] : F ≃+* AlgebraicClosure F :=
  RingEquiv.ofBijective (algebraMap F (AlgebraicClosure F))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem map_irreducible_iff {F σ : Type*} [Field F] [IsAlgClosed F]
    (P : MvPolynomial σ F) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) P) ↔ Irreducible P := by
  let e := closureEquiv F
  change Irreducible (mapEquiv σ e P) ↔ Irreducible P
  exact MulEquiv.irreducible_iff (mapEquiv σ e)

end PaperP1.AlgClosedPolynomialIrreducibility
