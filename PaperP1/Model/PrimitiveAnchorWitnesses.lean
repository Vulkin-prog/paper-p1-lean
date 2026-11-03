module

public import PaperP1.Affine.PrimitiveCoordinateProjection
public import PaperP1.Arithmetic.HeavyPhysicalRelations
public import PaperP1.Model.MultiAnchorRelationFamilies

/-! # Every primitive has block-dependent heavy physical relations up to its nullity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveAnchorWitnesses

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ConnectedWindowFamilies

local instance primitiveAnchorPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem witnesses (t L : ℕ) (ht : Even t) (I : Finset ℕ) (hprim : Primitive L I)
    (hpos : ∀ x ∈ I, 0 < x)
    (hdim : t - 1 ≤ relativeNullityOn (fun x ↦ squareClassSpace x L) I) (Y T : ℝ) :
    PaperP1.MultiAnchorRelationFamilies.Witnesses t (L + 1) Y T I := by
  intro a _hunmarked
  have hprojection := PaperP1.PrimitiveCoordinateProjection.finrank_range
    (fun x ↦ squareClassSpace x L) I hprim.2 a
  have hrank : t - 1 ≤ Module.finrank F₂
      (LinearMap.range (PaperP1.PhysicalWindowRelations.effectiveProjection
        (fun x : I ↦ x.val) L a)) := by
    exact hdim.trans_eq hprojection.symm
  exact PaperP1.HeavyPhysicalRelations.exists_relation (fun x : I ↦ x.val) L
    (fun x ↦ hpos x.val x.property) a t ht hrank

theorem two_witnesses (L : ℕ) (I : Finset ℕ) (hprim : Primitive L I)
    (hpos : ∀ x ∈ I, 0 < x) (Y T : ℝ) :
    PaperP1.MultiAnchorRelationFamilies.Witnesses 2 (L + 1) Y T I := by
  apply witnesses 2 L (by decide) I hprim hpos ?_ Y T
  have h := hprim.1
  omega

end PaperP1.PrimitiveAnchorWitnesses
