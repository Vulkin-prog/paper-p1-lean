module

public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Affine.RelationCoordinateSpan

/-! # Every member of a nontrivial connected family meets the span of its complement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTargetDependence

open Finset PaperP1.Arithmetic PaperP1.Affine

theorem every_target (L : ℕ) (I : Finset ℕ) (hsize : 2 ≤ I.card)
    (hconn : ConnectedWindowFamilies.Connected L I) {z : ℕ} (hz : z ∈ I) :
    squareClassSpace z L ⊓ SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) (I.erase z) ≠ ⊥ := by
  classical
  obtain ⟨y, hy, hyz⟩ := exists_mem_ne (by omega : 1 < I.card) z
  let i : I := ⟨z, hz⟩
  let j : I := ⟨y, hy⟩
  obtain ⟨u, hsum, hne⟩ := ConnectedRelations.coordinate_relation
    (fun x : I ↦ squareClassSpace x.val L) hconn i j (fun h ↦ hyz (congrArg Subtype.val h).symm)
  rw [← RelationCoordinateSpan.otherSpace_subtype (fun x ↦ squareClassSpace x L) I i]
  exact RelationCoordinateSpan.intersection_ne_bot _ u hsum i
    (fun h ↦ hne (congrArg Subtype.val h))

end PaperP1.ConnectedTargetDependence
