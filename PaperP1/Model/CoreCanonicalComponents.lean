module

public import PaperP1.Model.RelationCoreWitnesses
public import PaperP1.Model.ActualCanonicalComponents

/-! # Every actual positive-projection relation core has no singleton canonical component -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoreCanonicalComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RelationProjectionRank
  PaperP1.RelationCoreWitnesses PaperP1.ActualCanonicalComponents

theorem singleton_loss_zero (L : ℕ) (I : Finset ℕ) (i : I)
    (hi : {i} ∈ (canonicalRelationPartition (fun j : I ↦ squareClassSpace j.val L)).parts) :
    loss (fun x ↦ squareClassSpace x L) I i.val = 0 := by
  have hp : PrimitiveCoordinateProjection.projection (fun x ↦ squareClassSpace x L) I i = 0 := by
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    change (r.val i).val = 0
    have h := canonicalRelationPartition_respects (fun j : I ↦ squareClassSpace j.val L)
      r.val r.property {i} hi
    simpa only [sum_singleton] using h
  rw [loss_eq_dimension _ I i, hp, LinearMap.range_zero, finrank_bot]

theorem block_card (t L : ℕ) (ht : 2 ≤ t) (I : Finset ℕ) (hcore : Core t L I)
    (C : Finset ℕ) (hC : C ∈ blocks L I) : 2 ≤ C.card := by
  classical
  have hpos := card_pos.mpr (block_nonempty L I C hC)
  by_contra hn
  have hone : C.card = 1 := by omega
  obtain ⟨x, hCx⟩ := card_eq_one.mp hone
  have hx : x ∈ I := block_subset L I C hC (by rw [hCx]; exact mem_singleton_self x)
  let i : I := ⟨x, hx⟩
  obtain ⟨D, hD, hDC⟩ := mem_image.mp hC
  have hDi : D = {i} := by
    apply image_injective I
    change FinitePartImage.image D = FinitePartImage.image {i}
    rw [hDC, hCx]
    simp only [FinitePartImage.image, image_singleton, i]
  have hi : {i} ∈ (canonicalRelationPartition (fun j : I ↦ squareClassSpace j.val L)).parts := by
    simpa only [hDi] using hD
  have hzero := singleton_loss_zero L I i hi
  have h := hcore x hx
  change loss (fun x ↦ squareClassSpace x L) I x = 0 at hzero
  rw [hzero] at h
  omega

end PaperP1.CoreCanonicalComponents
