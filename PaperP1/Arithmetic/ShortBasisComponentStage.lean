module

public import PaperP1.Arithmetic.MediumPrimeColumns
public import PaperP1.Arithmetic.ComponentProjectionInjectivity
public import PaperP1.Model.FreeComponentRank

/-! # The actual component and medium-column stage of short-basis extraction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisComponentStage

open Finset PaperP1.Arithmetic PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution PaperP1.MediumPrimeColumns
  PaperP1.ComponentProjectionInjectivity PaperP1.FreeComponentRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

def freeComponents (x y L : ℕ) : Finset (largePrimeGraph x y L).ConnectedComponent :=
  nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)

def retainedComponents (x y L z M : ℕ) : Finset (largePrimeGraph x y L).ConnectedComponent :=
  DisjointColumnWeights.light (smallComponents x y L (freeComponents x y L) M)
    (fun c ↦ (column x y L z c).card)

theorem retained_subset_free (x y L z M : ℕ) :
    IsFreeFamily x y L (retainedComponents x y L z M) := by
  intro c hc
  exact (mem_filter.mp ((mem_filter.mp hc).1)).1

theorem retained_component_size (x y L z M : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : c ∈ retainedComponents x y L z M) : (componentVertices (largePrimeGraph x y L) c).card ≤ M :=
  (mem_filter.mp ((mem_filter.mp hc).1)).2

theorem retained_column_weight (x y L z M : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : c ∈ retainedComponents x y L z M) : (column x y L z c).card ≤ 2 :=
  (mem_filter.mp hc).2

theorem retained_card_lower (x y L z M : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (pairIntersectionRank x y L : ℝ) - defectiveVertexCount x y L -
      2 * (L + 1 : ℕ) / (M + 1 : ℕ) -
      (2 * (L + 1 : ℕ) * (∑ p ∈ mediumPrimes L z, 1 / (p : ℝ)) + 2 * (mediumPrimes L z).card) / 3 ≤
        ((retainedComponents x y L z M).card : ℝ) := by
  have hpair : (pairIntersectionRank x y L : ℝ) ≤
      (nontrivialComponentCount x y L : ℝ) + defectiveVertexCount x y L := by
    exact_mod_cast intersection_le_components_add_defects hx hy
  have hret := light_small_components_lower x y L z (freeComponents x y L) M (by omega) (by omega)
  change (nontrivialComponentCount x y L : ℝ) - _ - _ ≤ ((retainedComponents x y L z M).card : ℝ) at hret
  linarith

theorem physical_projections_injective (x y L z M : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Function.Injective (firstProjection x y L (retainedComponents x y L z M)) ∧
      Function.Injective (secondProjection x y L (retainedComponents x y L z M)) :=
  ⟨firstProjection_injective x y L _ hx hy (retained_subset_free x y L z M),
    secondProjection_injective x y L _ hx hy (retained_subset_free x y L z M)⟩

theorem first_square_classes_injective (x y L z M : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Function.Injective (firstClasses x y L (retainedComponents x y L z M)) :=
  firstClasses_injective x y L _ hx hy (retained_subset_free x y L z M)

theorem large_prime_equations (x y L z M : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (w : retainedComponents x y L z M → F₂) :
    ComponentSelection.selection (largePrimeGraph x y L) (retainedComponents x y L z M) w ∈
      largePrimeSolution x y L :=
  selection_mem_largePrimeSolution x y L _ hx hy (retained_subset_free x y L z M) w

end PaperP1.ShortBasisComponentStage
