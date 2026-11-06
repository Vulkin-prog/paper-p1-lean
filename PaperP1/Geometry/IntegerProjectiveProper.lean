module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Limits

/-! # The actual integer structure morphism of a finite-type graded algebra is proper -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerProjectiveProper

open AlgebraicGeometry CategoryTheory

variable {A : Type} [CommRing A]
    (G : ℕ → Submodule ℤ A) [GradedRing G]

def structureMap : Proj G ⟶ Spec (CommRingCat.of ℤ) :=
  Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (G 0)))

theorem proper [Algebra.FiniteType (G 0) A] [Module.Finite ℤ (G 0)] :
    IsProper (structureMap G) := by
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ (G 0)))) := by
    apply (IsFinite.SpecMap_iff _).mpr
    change (algebraMap ℤ (G 0)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  change IsProper (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (G 0))))
  infer_instance

end PaperP1.IntegerProjectiveProper
