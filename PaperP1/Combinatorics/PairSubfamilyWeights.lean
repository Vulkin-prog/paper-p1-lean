module

public import PaperP1.Combinatorics.OrderedPairTuples

/-! # Exact ordered-host sums over any selected family of two-element sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairSubfamilyWeights

open Finset

def hosts (G : Finset ℕ) (F : Finset (Finset ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (OrderedPairTuples.pairs G).filter fun p ↦ {p.1, p.2} ∈ F

theorem mem_hosts (G : Finset ℕ) (F : Finset (Finset ℕ)) (p : ℕ × ℕ) :
    p ∈ hosts G F ↔ p.1 ∈ G ∧ p.2 ∈ G ∧ p.1 ≠ p.2 ∧ {p.1, p.2} ∈ F := by
  classical
  simp only [hosts, OrderedPairTuples.pairs, mem_filter, mem_product]
  tauto

theorem weighted_sum (G : Finset ℕ) (F : Finset (Finset ℕ)) (hF : F ⊆ G.powersetCard 2)
    (w : Finset ℕ → ℝ) :
    (∑ p ∈ hosts G F, w {p.1, p.2}) = 2 * ∑ e ∈ F, w e := by
  classical
  have hfilter : (G.powersetCard 2).filter (fun e ↦ e ∈ F) = F := by
    ext e
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hF h, h⟩⟩
  calc
    _ = ∑ p ∈ OrderedPairTuples.pairs G, (if {p.1, p.2} ∈ F then w {p.1, p.2} else 0) := by
      rw [hosts, sum_filter]
    _ = 2 * ∑ e ∈ G.powersetCard 2, (if e ∈ F then w e else 0) :=
      OrderedPairTuples.weighted_subsets G (fun e ↦ if e ∈ F then w e else 0)
    _ = _ := by rw [← sum_filter, hfilter]

end PaperP1.PairSubfamilyWeights
