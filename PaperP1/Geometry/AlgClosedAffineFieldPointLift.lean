module

public import PaperP1.Geometry.AlgClosedFieldPointLift

/-! # Actual ring homomorphisms from nonempty affine fibres over algebraically closed fields -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.AlgClosedAffineFieldPointLift

open AlgebraicGeometry CategoryTheory

variable {R S K : Type u} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]

theorem exists_hom (f : R →+* S) (ε : R →+* K)
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom f))]
    (hε : PrimeSpectrum.comap ε (IsLocalRing.closedPoint K) ∈ Set.range (PrimeSpectrum.comap f)) :
    ∃ ψ : S →+* K, ψ.comp f = ε := by
  obtain ⟨x, hx⟩ := AlgClosedFieldPointLift.exists_lift
    (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom ε)) hε
  refine ⟨(Spec.preimage x).hom, ?_⟩
  have he : CommRingCat.ofHom f ≫ Spec.preimage x = CommRingCat.ofHom ε := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hx
  exact congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of K ↦ g.hom) he

end PaperP1.AlgClosedAffineFieldPointLift
