module

public import PaperP1.Combinatorics.OrderedPairTuples

/-! # The sum of all unordered pair rows counts every actual edge exactly twice -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnorderedPairRows

open Finset

theorem sum_rows {ι : Type*} [DecidableEq ι] (G : Finset ι) (w : Finset ι → ℝ) :
    (∑ x ∈ G, ∑ y ∈ G.erase x, w {x, y}) = 2 * ∑ e ∈ G.powersetCard 2, w e := by
  classical
  have h : (∑ p ∈ OrderedPairTuples.pairs G, w {p.1, p.2}) =
      ∑ x ∈ G, ∑ y ∈ G.erase x, w {x, y} := by
    rw [OrderedPairTuples.pairs, sum_filter, sum_product]
    apply sum_congr rfl
    intro x _
    dsimp only
    rw [← sum_filter]
    congr 1
    ext y
    simp only [mem_filter, mem_erase]
    tauto
  rw [← h, OrderedPairTuples.weighted_subsets]

end PaperP1.UnorderedPairRows
