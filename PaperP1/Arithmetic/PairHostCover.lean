module

public import PaperP1.Arithmetic.DependentBlockPairs
public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Model.RegularStarts

/-! # Actual full pair-rank loss is covered by effective dependence or a local defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairHostCover

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedPairRankLoss
  PaperP1.RegularStarts

local instance pairHostCoverTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def blocks (L : ℕ) : Fin 2 → ℕ → Finset ℕ := fun _ x ↦ NormalizedWindowSets.values x L

def hosts (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦ 0 < pairLoss p.1 p.2 L

theorem regular_loss_iff {N L x y : ℕ} (hx : x ∈ regularStarts N L)
    (hy : y ∈ regularStarts N L) :
    0 < pairLoss x y L ↔ DependentBlockPairs.Dependent (blocks L) (x, y) := by
  have hxrank := (mem_regularStarts.mp hx).2
  have hyrank := (mem_regularStarts.mp hy).2
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have heq : pairLoss x y L = Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) := by
    unfold pairLoss
    omega
  rw [heq, DependentBlockPairs.dependent_iff_intersection]
  simp only [blocks, NormalizedWindowSets.space_values]
  rw [Nat.pos_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero]

theorem cover (N L : ℕ) :
    hosts N L ⊆ DependentBlockPairs.pairs (dyadicBlock N) (blocks L) ∪
      ((irregularStarts N L ×ˢ dyadicBlock N) ∪ (dyadicBlock N ×ˢ irregularStarts N L)) := by
  classical
  intro p hp
  obtain ⟨hpbox, hloss⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hpbox
  by_cases hxreg : p.1 ∈ regularStarts N L
  · by_cases hyreg : p.2 ∈ regularStarts N L
    · exact mem_union_left _ (mem_filter.mpr ⟨hpbox, (regular_loss_iff hxreg hyreg).mp hloss⟩)
    · exact mem_union_right _ (mem_union_right _
        (mem_product.mpr ⟨hx, mem_sdiff.mpr ⟨hy, hyreg⟩⟩))
  · exact mem_union_right _ (mem_union_left _
      (mem_product.mpr ⟨mem_sdiff.mpr ⟨hx, hxreg⟩, hy⟩))

theorem card_bound (N L : ℕ) :
    (hosts N L).card ≤ (DependentBlockPairs.pairs (dyadicBlock N) (blocks L)).card +
      2 * (irregularStarts N L).card * N := by
  have h := (card_le_card (cover N L)).trans (card_union_le _ _)
  have hlocal := card_union_le (irregularStarts N L ×ˢ dyadicBlock N)
    (dyadicBlock N ×ˢ irregularStarts N L)
  have hdyadic : (dyadicBlock N).card = N := dyadicBlock_card N
  simp only [card_product, hdyadic] at hlocal
  nlinarith

end PaperP1.PairHostCover
