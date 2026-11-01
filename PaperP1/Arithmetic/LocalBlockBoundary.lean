module

public import PaperP1.Arithmetic.LocalRelationBlocks

/-! # Full local block lengths and the at most two endpoint truncations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlockBoundary

open Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.Arithmetic
  PaperP1.Model PaperP1.WindowRelationCode

def truncated (N L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (relations N L).filter fun S ↦ ¬fullBlock L S ⊆ dyadicBlock N

def leftTruncated (N L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (relations N L).filter fun S ↦ last S - L + 1 < N

def rightTruncated (N L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (relations N L).filter fun S ↦ 2 * N ≤ first S + 1

theorem block_subset_full {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) : block N L S ⊆ fullBlock L S := by
  rw [block_eq_interval hN S ((mem_relations N L S).mp hS).1.1 (last_ge_length hNL hS)]
  exact inter_subset_left

theorem fullBlock_nonempty {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) : (fullBlock L S).Nonempty :=
  (block_nonempty hS).mono (block_subset_full hN hNL hS)

theorem fullBlock_card {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    (fullBlock L S).card = L - (last S - first S) + 1 := by
  have hrel := ((mem_relations N L S).mp hS).1
  have hab := first_le_last hrel.1
  have hbL := last_ge_length hNL hS
  obtain ⟨x, hx⟩ := fullBlock_nonempty hN hNL hS
  have hbounds := mem_Icc.mp hx
  simp only [fullBlock, Nat.card_Icc]
  omega

theorem fullBlock_card_le_length {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) : (fullBlock L S).card ≤ L := by
  have hrel := ((mem_relations N L S).mp hS).1
  have hab := relation_first_lt_last hrel
  obtain ⟨x, hx⟩ := fullBlock_nonempty hN hNL hS
  have hbounds := mem_Icc.mp hx
  have hbL := last_ge_length hNL hS
  simp only [fullBlock, Nat.card_Icc]
  omega

theorem endpoint_mem_full {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) : first S + 1 ∈ fullBlock L S := by
  obtain ⟨x, hx⟩ := fullBlock_nonempty hN hNL hS
  have h := mem_Icc.mp hx
  exact mem_Icc.mpr ⟨by omega, le_rfl⟩

theorem block_eq_full_of_subset {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) (hfull : fullBlock L S ⊆ dyadicBlock N) :
    block N L S = fullBlock L S := by
  rw [block_eq_interval hN S ((mem_relations N L S).mp hS).1.1 (last_ge_length hNL hS)]
  exact inter_eq_left.mpr hfull

theorem left_endpoint_mem {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ leftTruncated N L) : N ∈ block N L S := by
  obtain ⟨hS, hleft⟩ := mem_filter.mp hS
  rw [block_eq_interval hN S ((mem_relations N L S).mp hS).1.1 (last_ge_length hNL hS)]
  obtain ⟨x, hx⟩ := block_nonempty hS
  obtain ⟨hxbox, hxwin⟩ := (mem_block N L S x).mp hx
  have hxpos : 0 < x := by have h := (mem_Ico.mp hxbox).1; omega
  have hupper := ((subset_window_iff hxpos S ((mem_relations N L S).mp hS).1.1).mp hxwin).1
  have hxN := (mem_Ico.mp hxbox).1
  exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩

theorem right_endpoint_mem {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ rightTruncated N L) : 2 * N - 1 ∈ block N L S := by
  obtain ⟨hS, hright⟩ := mem_filter.mp hS
  have heq := block_eq_interval hN S ((mem_relations N L S).mp hS).1.1 (last_ge_length hNL hS)
  obtain ⟨x, hx⟩ := block_nonempty hS
  rw [heq] at hx ⊢
  obtain ⟨hxfull, hxbox⟩ := mem_inter.mp hx
  have hlow := (mem_Icc.mp hxfull).1
  have hxhi := (mem_Ico.mp hxbox).2
  exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Ico.mpr ⟨by omega, by omega⟩⟩

theorem leftTruncated_card_le_one {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    (leftTruncated N L).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro S hS T hT
  by_contra hne
  have hdis := blocks_disjoint hN hrank (mem_filter.mp hS).1 (mem_filter.mp hT).1 hne
  exact disjoint_left.mp hdis (left_endpoint_mem hN hNL hS) (left_endpoint_mem hN hNL hT)

theorem rightTruncated_card_le_one {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    (rightTruncated N L).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro S hS T hT
  by_contra hne
  have hdis := blocks_disjoint hN hrank (mem_filter.mp hS).1 (mem_filter.mp hT).1 hne
  exact disjoint_left.mp hdis (right_endpoint_mem hN hNL hS) (right_endpoint_mem hN hNL hT)

theorem truncated_subset_sides (N L : ℕ) : truncated N L ⊆ leftTruncated N L ∪ rightTruncated N L := by
  classical
  intro S hS
  obtain ⟨hS, hnot⟩ := mem_filter.mp hS
  obtain ⟨x, hxfull, hxnot⟩ := not_subset.mp hnot
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hxfull
  by_cases hx : x < N
  · exact mem_union_left _ (mem_filter.mpr ⟨hS, by omega⟩)
  · have hxright : 2 * N ≤ x := by
      by_contra h
      exact hxnot (mem_Ico.mpr ⟨by omega, by omega⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨hS, by omega⟩)

theorem truncated_card_le_two {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    (truncated N L).card ≤ 2 := by
  have hleft := leftTruncated_card_le_one hN hNL hrank
  have hright := rightTruncated_card_le_one hN hNL hrank
  have hsub := card_le_card (truncated_subset_sides N L)
  have hunion : (leftTruncated N L ∪ rightTruncated N L).card ≤
      (leftTruncated N L).card + (rightTruncated N L).card := card_union_le _ _
  omega

end PaperP1.LocalBlockBoundary
