module

public import PaperP1.Model.DirectRunBlocks
public import PaperP1.Model.FourthRunComponents
public import PaperP1.Combinatorics.PairFinpartition

/-! # A nonzero direct pair-product decomposition is uniquely canonical -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalPairImages

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

set_option maxHeartbeats 1000000 in
theorem canonical_images (L : ℕ) (hL : 0 < L) (e f : Finset ℕ)
    (he : e.card = 2) (hf : f.card = 2) (hef : Disjoint e f)
    (hnull : runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f)
    (hc : infiniteCenteredCoefficient L (e ∪ f) ≠ 0) :
    (canonicalRelationPartition (fun i : ↥(e ∪ f) ↦ squareClassSpace i.val L)).parts.image
      (fun C ↦ FinitePartImage.image C) = {e, f} := by
  classical
  let I := e ∪ f
  let S := fun i : I ↦ squareClassSpace i.val L
  let Q := canonicalRelationPartition S
  let M := I.sup fun x ↦ x + L
  obtain ⟨P, C, D, hP, hparts, _hCD, hCe, hDf⟩ := DirectRunBlocks.exists_partition L e f
    (card_pos.mp (by omega)) (card_pos.mp (by omega)) hef hnull
  have hPcard : ∀ E ∈ P.parts, E.card = 2 := by
    intro E hE
    rw [hparts] at hE
    simp only [mem_insert, mem_singleton] at hE
    rcases hE with hEC | hED
    · rw [hEC, ← FinitePartImage.card_image C, hCe, he]
    · rw [hED, ← FinitePartImage.card_image D, hDf, hf]
  have hp := FourthRunComponents.positive_marginals L I hc
  have hcut (i : I) : i.val + L ≤ M := le_sup (f := fun x ↦ x + L) i.property
  have hcenter : infiniteFamilyCenteredMoment L (fun i : I ↦ i.val) ≠ 0 := by
    rwa [← infiniteCenteredCoefficient_eq_family_subtype]
  obtain ⟨s, hs⟩ := squareClass_full_relation_of_ne_zero M L (fun i : I ↦ i.val) hL hcut
    (fun i ↦ hp i.val i.property) hcenter
  have hnosingle := TripleFullSupportConnected.no_singleton_part S s hs Q
    (canonicalRelationPartition_respects S)
  have hQlower : ∀ E ∈ Q.parts, 2 ≤ E.card := by
    intro E hE
    have hpos := card_pos.mpr (Q.nonempty_of_mem_parts hE)
    have hne := hnosingle E hE
    omega
  have hQP : Q = P := PairFinpartition.eq_of_pair_refinement Q P
    (canonicalRelationPartition_le S P hP) hQlower hPcard
  change Q.parts.image (fun E ↦ FinitePartImage.image E) = {e, f}
  rw [hQP, hparts]
  simp only [image_insert, image_singleton, hCe, hDf]

end PaperP1.CanonicalPairImages
