module

public import PaperP1.Combinatorics.GraphStarWeights
public import Mathlib.Data.Finset.Card

/-! # Actual finite families above prescribed sources are covered by their actual two-target extensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetFamilyCover

open Finset

def family (E : Finset ℕ) (p : ℕ × ℕ) : Finset ℕ := insert p.1 (insert p.2 E)

def pairs (G E : Finset ℕ) (F : Finset (Finset ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (G ×ˢ G).filter fun p ↦ p.1 ≠ p.2 ∧ p.1 ∉ E ∧ p.2 ∉ E ∧ family E p ∈ F

theorem mem_pairs (G E : Finset ℕ) (F : Finset (Finset ℕ)) (p : ℕ × ℕ) :
    p ∈ pairs G E F ↔ p.1 ∈ G ∧ p.2 ∈ G ∧ p.1 ≠ p.2 ∧ p.1 ∉ E ∧ p.2 ∉ E ∧ family E p ∈ F := by
  classical
  simp only [pairs, mem_filter, mem_product]
  exact and_assoc

theorem exists_pair {G E I : Finset ℕ} (hIG : I ⊆ G) (hEI : E ⊆ I) (hcard : I.card = E.card + 2) :
    ∃ p : ℕ × ℕ, p.1 ∈ G ∧ p.2 ∈ G ∧ p.1 ≠ p.2 ∧ p.1 ∉ E ∧ p.2 ∉ E ∧ family E p = I := by
  have hdiff : (I \ E).card = 2 := by rw [card_sdiff_of_subset hEI, hcard]; omega
  obtain ⟨y, z, hyz, hset⟩ := card_eq_two.mp hdiff
  have hy : y ∈ I \ E := by rw [hset]; exact mem_insert_self _ _
  have hz : z ∈ I \ E := by rw [hset]; exact mem_insert_of_mem (mem_singleton_self _)
  have heq := sdiff_union_of_subset hEI
  rw [hset] at heq
  refine ⟨(y, z), hIG (mem_sdiff.mp hy).1, hIG (mem_sdiff.mp hz).1, hyz,
    (mem_sdiff.mp hy).2, (mem_sdiff.mp hz).2, ?_⟩
  simpa only [family, insert_union, singleton_union] using heq

theorem extension_sum_le (G E : Finset ℕ) (F : Finset (Finset ℕ)) (w : Finset ℕ → ℝ)
    (hw : ∀ I, 0 ≤ w I) (hF : ∀ I ∈ F, I ⊆ G ∧ E ⊆ I ∧ I.card = E.card + 2) :
    (∑ I ∈ F, w I) ≤ ∑ p ∈ pairs G E F, w (family E p) := by
  classical
  have hsub : F ⊆ (pairs G E F).image (family E) := by
    intro I hI
    obtain ⟨p, hpG, hqG, hpq, hpE, hqE, heq⟩ := exists_pair (hF I hI).1 (hF I hI).2.1 (hF I hI).2.2
    exact mem_image.mpr ⟨p, (mem_pairs G E F p).mpr ⟨hpG, hqG, hpq, hpE, hqE, heq.symm ▸ hI⟩, heq⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ hw I)).trans
    (sum_image_le_of_nonneg (fun I _ ↦ hw I))

theorem weighted_cover (G : Finset ℕ) (C F : Finset (Finset ℕ)) (w : Finset ℕ → ℝ)
    (hw : ∀ I, 0 ≤ w I) (hG : ∀ I ∈ F, I ⊆ G)
    (hgap : ∀ E ∈ C, ∀ I ∈ F, I.card = E.card + 2)
    (hcover : ∀ I ∈ F, ∃ E ∈ C, E ⊆ I) :
    (∑ I ∈ F, w I) ≤ ∑ E ∈ C, ∑ p ∈ pairs G E F, w (family E p) := by
  classical
  let extensions := fun E : Finset ℕ ↦ F.filter fun I ↦ E ⊆ I
  have hsub : F ⊆ C.biUnion extensions := by
    intro I hI
    obtain ⟨E, hE, hEI⟩ := hcover I hI
    exact mem_biUnion.mpr ⟨E, hE, mem_filter.mpr ⟨hI, hEI⟩⟩
  calc
    _ ≤ ∑ I ∈ C.biUnion extensions, w I := sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ hw I)
    _ ≤ ∑ E ∈ C, ∑ I ∈ extensions E, w I := GraphStarWeights.sum_biUnion_le_nonneg C extensions w hw
    _ ≤ ∑ E ∈ C, ∑ p ∈ pairs G E (extensions E), w (family E p) := by
      apply sum_le_sum
      intro E hE
      apply extension_sum_le G E (extensions E) w hw
      intro I hI
      exact ⟨hG I (mem_filter.mp hI).1, (mem_filter.mp hI).2, hgap E hE I (mem_filter.mp hI).1⟩
    _ ≤ ∑ E ∈ C, ∑ p ∈ pairs G E F, w (family E p) := by
      apply sum_le_sum
      intro E _hE
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpG, hqG, hpq, hpE, hqE, hpF⟩ := (mem_pairs G E (extensions E) p).mp hp
        exact (mem_pairs G E F p).mpr ⟨hpG, hqG, hpq, hpE, hqE, (mem_filter.mp hpF).1⟩
      · intro p _ _
        exact hw _

end PaperP1.TwoTargetFamilyCover
