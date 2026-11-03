module

public import PaperP1.Affine.DirectBlockDisjoint
public import PaperP1.Model.ActualCanonicalComponents
public import PaperP1.Model.FourthRunComponents
public import PaperP1.Model.ConnectedSeedCatalog
public import PaperP1.Affine.FinitePartPreimage

/-! # Every actual family without singleton canonical components and of size at least three contains a controlled seed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NoSingletonSeedCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies PaperP1.ActualCanonicalComponents

theorem distinct_blocks (L : ℕ) (I C D : Finset ℕ)
    (hC : C ∈ blocks L I) (hD : D ∈ blocks L I) (hne : C ≠ D) :
    Disjoint C D ∧ Disjoint (span (fun x ↦ squareClassSpace x L) C) (span (fun x ↦ squareClassSpace x L) D) := by
  classical
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
  have hAB : A ≠ B := fun h ↦ hne (congrArg FinitePartImage.image h)
  have hdis := (canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).disjoint hA hB hAB
  have hspace := DirectBlockDisjoint.partition_parts (fun i : I ↦ squareClassSpace i.val L) _
    (canonicalRelationPartition_respects _) A B hA hB hAB
  rw [FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) A,
    FinitePartPreimage.span_image (fun x ↦ squareClassSpace x L) B] at hspace
  exact ⟨FourthRunComponents.images_disjoint hdis, hspace⟩

theorem cover (G : Finset ℕ) (L R : ℕ) (I : Finset ℕ) (hIG : I ⊆ G)
    (hsize : 3 ≤ I.card) (hcap : I.card ≤ R)
    (hparts : ∀ C ∈ blocks L I, 2 ≤ C.card) :
    ∃ D ∈ ConnectedSeedCatalog.families G L R, D ⊆ I := by
  classical
  by_cases hlarge : ∃ C ∈ blocks L I, 3 ≤ C.card
  · obtain ⟨C, hC, hthree⟩ := hlarge
    have hCI := block_subset L I C hC
    obtain ⟨D, hD, hDC⟩ := ConnectedSeedCatalog.cover G L R C (hCI.trans hIG) hthree
      ((card_le_card hCI).trans hcap) (block_connected L I C hC)
    exact ⟨D, hD, hDC.trans hCI⟩
  have htwo (C : Finset ℕ) (hC : C ∈ blocks L I) : C.card = 2 := by
    have hlo := hparts C hC
    have hhi : ¬ 3 ≤ C.card := fun h ↦ hlarge ⟨C, hC, h⟩
    omega
  have hcount : 2 ≤ (blocks L I).card := by
    have h := card_biUnion_le (s := blocks L I) (t := id)
    rw [union_blocks] at h
    have hs : (∑ C ∈ blocks L I, C.card) = 2 * (blocks L I).card := by
      rw [sum_congr rfl (fun C hC ↦ htwo C hC), sum_const, smul_eq_mul]
      omega
    change I.card ≤ ∑ C ∈ blocks L I, C.card at h
    rw [hs] at h
    omega
  obtain ⟨C, hC, D, hD, hCD⟩ := one_lt_card.mp (show 1 < (blocks L I).card by omega)
  have hCI := block_subset L I C hC
  have hDI := block_subset L I D hD
  obtain ⟨hsetDis, hspaceDis⟩ := distinct_blocks L I C D hC hD hCD
  have hdepC := CrossingPairTriple.connected_positive L C (by rw [htwo C hC]) (block_connected L I C hC)
  have hdepD := CrossingPairTriple.connected_positive L D (by rw [htwo D hD]) (block_connected L I D hD)
  have hCMem : C ∈ DependentFamilySeeds.dependentFamilies G L 2 :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hCI.trans hIG, htwo C hC⟩, hdepC⟩
  have hDMem : D ∈ DependentFamilySeeds.dependentFamilies G L 2 :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, htwo D hD⟩, hdepD⟩
  have hlow : C ∪ D ∈ LowTwoPairSeeds.families G L (1 / 12) := by
    refine mem_image.mpr ⟨(C, D), (LowTwoPairSeeds.mem_sourcePairs G L (1 / 12) (C, D)).mpr
      ⟨hCMem, hDMem, hsetDis, ?_⟩, rfl⟩
    rw [hspaceDis.eq_bot, finrank_bot, Nat.cast_zero]
    positivity
  exact ⟨C ∪ D, mem_union_left _ (mem_union_left _ (mem_union_right _ hlow)), union_subset hCI hDI⟩

end PaperP1.NoSingletonSeedCover
