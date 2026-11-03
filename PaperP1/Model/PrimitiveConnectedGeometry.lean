module

public import PaperP1.Model.SecondOrderRetainedClass
public import PaperP1.Model.PrimitiveWindowMass

/-! # Primitive original families are connected and their compatible nullity is at most one window rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveConnectedGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem connected (L : ℕ) (I : Finset ℕ) (hI : Primitive L I) : Connected L I := by
  classical
  by_contra hnot
  let P := canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)
  have hnull := UnrestrictedRunComponents.nullity_partition L I P (canonicalRelationPartition_respects _)
  have hz : ∀ D ∈ P.parts, runRelativeNullity L (FinitePartImage.image D) = 0 := by
    intro D hD
    let C := FinitePartImage.image D
    have hC : C ∈ ActualCanonicalComponents.blocks L I := mem_image.mpr ⟨D, hD, rfl⟩
    have hne : C ≠ I := by
      intro heq
      exact hnot (heq ▸ ActualCanonicalComponents.block_connected L I C hC)
    exact hI.2 C (Finset.ssubset_iff_subset_ne.mpr ⟨ActualCanonicalComponents.block_subset L I C hC, hne⟩)
  rw [sum_eq_zero hz] at hnull
  exact (Nat.ne_of_gt hI.1) hnull

theorem compatible_nullity_le {N L : ℕ} (hN : 0 < N) (I : Finset ℕ) (hIG : I ⊆ dyadicBlock N)
    (hI : Primitive L I) : runCompatibleNullity L I ≤ L := by
  have hcard := PrimitiveActiveSeeds.primitive_card_ge_two L I hI
  have hne : I.Nonempty := card_pos.mp (by omega)
  have hpos : ∀ x ∈ I, 0 < x := by intro x hx; have h := (mem_Ico.mp (hIG hx)).1; omega
  exact (runCompatibleNullity_le_relative L I).trans (PrimitiveWindowMass.primitive_nullity_le L I hne hI hpos)

end PaperP1.PrimitiveConnectedGeometry
