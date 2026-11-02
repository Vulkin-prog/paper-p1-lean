module

public import PaperP1.Affine.FourthFullSupportComponents
public import PaperP1.Model.FinitePartMoments
public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Model.ConnectedWindowFamilies

/-! # A nonconnected nonzero actual quartic coefficient factors over two direct pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRunComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem positive_marginals (L : ℕ) (I : Finset ℕ) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    ∀ x ∈ I, 0 < infiniteMarginal x L := by
  intro x hx
  by_contra h
  have hz : infiniteMarginal x L = 0 := le_antisymm (le_of_not_gt h)
    (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  exact hc (PositiveMarginalRestriction.zero_centered L I x hx hz)

theorem images_disjoint {I : Finset ℕ} {C D : Finset I} (hCD : Disjoint C D) :
    Disjoint (FinitePartImage.image C) (FinitePartImage.image D) := by
  apply disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨i, hi, hix⟩ := mem_image.mp hxC
  obtain ⟨j, hj, hjx⟩ := mem_image.mp hxD
  have hij : i = j := Subtype.ext (hix.trans hjx.symm)
  exact disjoint_left.mp hCD hi (hij ▸ hj)

theorem images_union {I : Finset ℕ} {C D : Finset I} (hCD : C ∪ D = univ) :
    FinitePartImage.image C ∪ FinitePartImage.image D = I := by
  change C.image Subtype.val ∪ D.image Subtype.val = I
  rw [← image_union, hCD]
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact i.property
  · intro hx
    exact mem_image.mpr ⟨⟨x, hx⟩, mem_univ _, rfl⟩

set_option maxHeartbeats 1000000 in
theorem disconnected_factorization (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.card = 4)
    (hc : infiniteCenteredCoefficient L I ≠ 0) (hconn : ¬ConnectedWindowFamilies.Connected L I) :
    ∃ e f : Finset ℕ, e.card = 2 ∧ f.card = 2 ∧ Disjoint e f ∧ e ∪ f = I ∧
      runRelativeNullity L I = runRelativeNullity L e + runRelativeNullity L f ∧
      infiniteCenteredCoefficient L I = infiniteCenteredCoefficient L e * infiniteCenteredCoefficient L f := by
  classical
  let M := I.sup fun x ↦ x + L
  let S := fun i : I ↦ squareClassSpace i.val L
  let P := canonicalRelationPartition S
  have hp := positive_marginals L I hc
  have hcut (i : I) : i.val + L ≤ M := le_sup (f := fun x ↦ x + L) i.property
  have hcenter : infiniteFamilyCenteredMoment L (fun i : I ↦ i.val) ≠ 0 := by
    rwa [← infiniteCenteredCoefficient_eq_family_subtype]
  obtain ⟨s, hs⟩ := squareClass_full_relation_of_ne_zero M L (fun i : I ↦ i.val) hL hcut
    (fun i ↦ hp i.val i.property) hcenter
  have hclass := FourthFullSupportComponents.connected_or_two_pairs S
    (by simpa only [Fintype.card_coe] using hI) s hs
  rcases hclass with htop | ⟨C, D, hCD, hparts, hCcard, hDcard⟩
  · exact False.elim (hconn htop)
  · change P.parts = {C, D} at hparts
    have hC : C ∈ P.parts := by rw [hparts]; exact mem_insert_self _ _
    have hD : D ∈ P.parts := by rw [hparts]; exact mem_insert_of_mem (mem_singleton_self _)
    have hdis : Disjoint C D := P.disjoint hC hD hCD
    have hunion : C ∪ D = univ := by
      have h := P.biUnion_parts
      rw [hparts, biUnion_insert, singleton_biUnion] at h
      exact h
    have hrel : runRelativeNullity L I = ∑ E ∈ P.parts,
        runRelativeNullity L (FinitePartImage.image E) := by
      calc
        _ = ∑ E : P.parts, relativeNullity (fun i : E.val ↦ S i.val) := relativeNullity_canonical_additive S
        _ = ∑ E : P.parts, runRelativeNullity L (FinitePartImage.image E.val) := by
          apply sum_congr rfl
          intro E _
          exact FinitePartImage.nullity_image (fun x ↦ squareClassSpace x L) E.val
        _ = _ := sum_coe_sort P.parts (fun E : Finset I ↦ runRelativeNullity L (FinitePartImage.image E))
    rw [hparts, sum_pair hCD] at hrel
    have hfactor : infiniteCenteredCoefficient L I = ∏ E ∈ P.parts,
        infiniteCenteredCoefficient L (FinitePartImage.image E) := by
      calc
        _ = ∏ E : P.parts, infiniteFamilyCenteredMoment L (fun i : E.val ↦ i.val.val) := by
          rw [infiniteCenteredCoefficient_eq_family_subtype]
          exact infiniteFamilyCenteredMoment_partition M L (fun i : I ↦ i.val) hL hcut
            (fun i ↦ hp i.val i.property) P (canonicalRelationPartition_respects S)
        _ = ∏ E : P.parts, infiniteCenteredCoefficient L (FinitePartImage.image E.val) := by
          apply prod_congr rfl
          intro E _
          exact (FinitePartMoments.centered_image L E.val).symm
        _ = _ := prod_coe_sort P.parts (fun E : Finset I ↦ infiniteCenteredCoefficient L (FinitePartImage.image E))
    rw [hparts, prod_pair hCD] at hfactor
    refine ⟨FinitePartImage.image C, FinitePartImage.image D, ?_, ?_, images_disjoint hdis,
      images_union hunion, hrel, hfactor⟩
    · rw [FinitePartImage.card_image, hCcard]
    · rw [FinitePartImage.card_image, hDcard]

end PaperP1.FourthRunComponents
