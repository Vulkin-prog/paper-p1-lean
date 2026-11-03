module

public import PaperP1.Combinatorics.FourVertexBudget
public import PaperP1.Combinatorics.TwoWindowGraphSwap
public import PaperP1.Asymptotics.GeneralTwoBlockComponentHostData
public import PaperP1.Asymptotics.DegreeOneGraphHostCount
public import PaperP1.Arithmetic.RawPairRelationRank

/-! # Actual small-component populations control the full two-window relation rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoWindowComponentSizeBudget

open Finset PaperP1.Arithmetic PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution
  PaperP1.PinnedGraphResolution PaperP1.TwoBlockComponentSquares

local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

def sizeComponents (x y L t : ℕ) : Finset (largePrimeGraph x y L).ConnectedComponent := by
  classical
  exact (nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)).filter
    fun c ↦ (vertices x y L c).card = t

theorem size_min {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : c ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) :
    2 ≤ (vertices x y L c).card := by
  obtain ⟨hl, hr⟩ := GeneralTwoBlockComponentHostData.offsets_nonempty hx hy c hc
  have hlc := hl.card_pos
  have hrc := hr.card_pos
  have hsum := GeneralTwoBlockComponentHostData.total_card x y L c
  omega

theorem four_vertex_budget {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    4 * nontrivialComponentCount x y L ≤ 2 * (L + 1) +
      2 * (sizeComponents x y L 2).card + (sizeComponents x y L 3).card := by
  have h := FourVertexBudget.budget Finset.univ
    (nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L))
    (vertices x y L) (fun _ _ ↦ subset_univ _)
    (MediumPrimeColumns.componentVertices_disjoint (largePrimeGraph x y L) _)
    (size_min hx hy)
  simpa only [nontrivialComponentCount, sizeComponents, card_univ, LargePrimeGraphResolution.card_occurrence] using h

theorem two_subset {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    sizeComponents x y L 2 ⊆ DegreeOneGraphHostCount.components x y L 1 := by
  intro c hc
  obtain ⟨hfree, hsize⟩ := mem_filter.mp hc
  obtain ⟨hl, hr⟩ := GeneralTwoBlockComponentHostData.offsets_nonempty hx hy c hfree
  have hlc : 0 < (vertices x y L c).toLeft.card := by
    rw [← TwoBlockComponentPatterns.left_card]
    exact hl.card_pos
  have hrc : 0 < (vertices x y L c).toRight.card := by
    rw [← TwoBlockComponentPatterns.right_card]
    exact hr.card_pos
  have hsum := card_toLeft_add_card_toRight (u := vertices x y L c)
  apply (DegreeOneGraphHostCount.mem_components x y L 1 c).mpr
  exact ⟨((mem_nontrivialUnpinnedComponents _).mp hfree).1, by omega, by omega⟩

theorem three_orientation {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) (hc : c ∈ sizeComponents x y L 3) :
    c ∈ DegreeOneGraphHostCount.components x y L 2 ∨
      TwoWindowGraphSwap.componentEquiv x y L c ∈ DegreeOneGraphHostCount.components y x L 2 := by
  obtain ⟨hfree, hsize⟩ := mem_filter.mp hc
  obtain ⟨hl, hr⟩ := GeneralTwoBlockComponentHostData.offsets_nonempty hx hy c hfree
  have hlc : 0 < (vertices x y L c).toLeft.card := by
    rw [← TwoBlockComponentPatterns.left_card]
    exact hl.card_pos
  have hrc : 0 < (vertices x y L c).toRight.card := by
    rw [← TwoBlockComponentPatterns.right_card]
    exact hr.card_pos
  have hsum := card_toLeft_add_card_toRight (u := vertices x y L c)
  have hn := ((mem_nontrivialUnpinnedComponents _).mp hfree).1
  by_cases hleft : (vertices x y L c).toLeft.card = 2
  · exact Or.inl ((DegreeOneGraphHostCount.mem_components x y L 2 c).mpr ⟨hn, hleft, by omega⟩)
  · apply Or.inr
    apply (DegreeOneGraphHostCount.mem_components y x L 2 _).mpr
    refine ⟨fun hp ↦ hn ((TwoWindowGraphSwap.component_pinned_swap x y L c).mp hp), ?_, ?_⟩
    · rw [TwoWindowGraphSwap.left_vertices_swap]
      omega
    · rw [TwoWindowGraphSwap.right_vertices_swap]
      omega

theorem three_card_bound {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (sizeComponents x y L 3).card ≤ (DegreeOneGraphHostCount.components x y L 2).card +
      (DegreeOneGraphHostCount.components y x L 2).card := by
  classical
  let Q := sizeComponents x y L 3
  let A := Q.filter fun c ↦ c ∈ DegreeOneGraphHostCount.components x y L 2
  let B := Q \ A
  have hA : A.card ≤ (DegreeOneGraphHostCount.components x y L 2).card :=
    card_le_card (fun _ hc ↦ (mem_filter.mp hc).2)
  have hB : B.card ≤ (DegreeOneGraphHostCount.components y x L 2).card := by
    apply card_le_card_of_injOn (TwoWindowGraphSwap.componentEquiv x y L)
    · intro c hc
      obtain ⟨hcQ, hcA⟩ := mem_sdiff.mp hc
      rcases three_orientation hx hy c hcQ with hleft | hright
      · exact False.elim (hcA (mem_filter.mpr ⟨hcQ, hleft⟩))
      · exact hright
    · exact (TwoWindowGraphSwap.componentEquiv x y L).injective.injOn
  have hp : B.card + A.card = Q.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  dsimp only [Q] at hp
  omega

theorem full_rank_bound {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    4 * RawPairRelationRank.fullRank x y L ≤ 4 * defectiveVertexCount x y L + 2 * (L + 1) +
      2 * (DegreeOneGraphHostCount.components x y L 1).card +
      (DegreeOneGraphHostCount.components x y L 2).card +
      (DegreeOneGraphHostCount.components y x L 2).card := by
  have hr := RawPairRelationRank.rank_le_components (L := L) hx hy
  have hp := four_vertex_budget (L := L) hx hy
  have htwo := card_le_card (two_subset (L := L) hx hy)
  have hthree := three_card_bound (L := L) hx hy
  omega

end PaperP1.TwoWindowComponentSizeBudget
