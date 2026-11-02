module

public import PaperP1.Model.UnrestrictedRunComponents
public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Affine.CanonicalPartConnected
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Actual original canonical blocks, nonzero factors and connectedness at every finite order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualCanonicalComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

def blocks (L : ℕ) (I : Finset ℕ) : Finset (Finset ℕ) :=
  (canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).parts.image
    (fun C : Finset I ↦ FinitePartImage.image C)

theorem image_injective (I : Finset ℕ) :
    Function.Injective (fun C : Finset I ↦ FinitePartImage.image C) :=
  Finset.image_injective Subtype.val_injective

theorem card_blocks (L : ℕ) (I : Finset ℕ) :
    (blocks L I).card = (canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).parts.card :=
  card_image_of_injective _ (image_injective I)

theorem union_blocks (L : ℕ) (I : Finset ℕ) : (blocks L I).biUnion id = I := by
  classical
  let P := canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hx
    obtain ⟨D, _hD, rfl⟩ := mem_image.mp hC
    exact FinitePartImage.image_subset D hxC
  · intro hx
    obtain ⟨C, hC, hiC⟩ := P.exists_mem (mem_univ (⟨x, hx⟩ : I))
    exact mem_biUnion.mpr ⟨FinitePartImage.image C, mem_image.mpr ⟨C, hC, rfl⟩,
      mem_image.mpr ⟨⟨x, hx⟩, hiC, rfl⟩⟩

theorem block_subset (L : ℕ) (I C : Finset ℕ) (hC : C ∈ blocks L I) : C ⊆ I := by
  obtain ⟨D, _, rfl⟩ := mem_image.mp hC
  exact FinitePartImage.image_subset D

theorem block_nonempty (L : ℕ) (I C : Finset ℕ) (hC : C ∈ blocks L I) : C.Nonempty := by
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
  exact FinitePartImage.image_nonempty
    ((canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).nonempty_of_mem_parts hD)

theorem block_connected (L : ℕ) (I C : Finset ℕ) (hC : C ∈ blocks L I) :
    ConnectedWindowFamilies.Connected L C := by
  classical
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
  obtain ⟨i, hi⟩ := (canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).nonempty_of_mem_parts hD
  let _ : Nonempty D := ⟨⟨i, hi⟩⟩
  exact FinitePartImage.connected_image (fun x ↦ squareClassSpace x L) D
    (CanonicalPartConnected.part_connected (fun i : I ↦ squareClassSpace i.val L) hD)

theorem coefficient_factor (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    infiniteCenteredCoefficient L I = ∏ C ∈ blocks L I, infiniteCenteredCoefficient L C := by
  rw [blocks, prod_image (image_injective I).injOn]
  exact UnrestrictedRunComponents.centered_partition L hL I _
    (canonicalRelationPartition_respects _)

theorem absolute_factor (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    |infiniteCenteredCoefficient L I| = ∏ C ∈ blocks L I, |infiniteCenteredCoefficient L C| := by
  rw [coefficient_factor L hL I, abs_prod]

theorem singleton_zero (L x : ℕ) : infiniteCenteredCoefficient L {x} = 0 := by
  rw [InfiniteTripleCancellation.coefficient_eq_transform]
  exact Algebra.centeredCoefficient_singleton_eq_zero _ _ x (infiniteJointMoment_empty L)
    (InfiniteTripleCancellation.singleton_joint L x)

theorem nonzero_block_card (L : ℕ) (hL : 0 < L) (I C : Finset ℕ)
    (hc : infiniteCenteredCoefficient L I ≠ 0) (hC : C ∈ blocks L I) : 2 ≤ C.card := by
  have hprod : (∏ D ∈ blocks L I, infiniteCenteredCoefficient L D) ≠ 0 := by
    rwa [← coefficient_factor L hL I]
  have hcn : infiniteCenteredCoefficient L C ≠ 0 := prod_ne_zero_iff.mp hprod C hC
  have hpos := card_pos.mpr (block_nonempty L I C hC)
  by_contra h
  have hone : C.card = 1 := by omega
  obtain ⟨x, rfl⟩ := card_eq_one.mp hone
  exact hcn (singleton_zero L x)

theorem nonconnected_card (L : ℕ) (I : Finset ℕ) (hI : I.Nonempty)
    (hconn : ¬ConnectedWindowFamilies.Connected L I) : 2 ≤ (blocks L I).card := by
  classical
  let P := canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)
  rw [card_blocks]
  change 2 ≤ P.parts.card
  obtain ⟨x, hx⟩ := hI
  have huniv : (univ : Finset I).Nonempty := ⟨⟨x, hx⟩, mem_univ _⟩
  have hpos := card_pos.mpr (P.parts_nonempty huniv.ne_empty)
  by_contra hn
  have hone : P.parts.card = 1 := by omega
  obtain ⟨C, hparts⟩ := card_eq_one.mp hone
  have hC : C = univ := by
    have h := P.biUnion_parts
    rw [hparts, singleton_biUnion] at h
    exact h
  apply hconn
  apply top_le_iff.mp
  intro D hD
  refine ⟨C, by rw [hparts]; exact mem_singleton_self _, ?_⟩
  rw [hC]
  exact subset_univ _

end PaperP1.ActualCanonicalComponents
