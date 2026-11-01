module

public import PaperP1.Arithmetic.ConnectedBlockLists
public import PaperP1.Asymptotics.RelativeBlockRelationsCount

/-! # Actual canonically connected finite effective block tuples have half-counts

The actual original-window family/marginal alignment for main 10.2 is
recorded separately; this theorem counts the actual generic block tuples.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedBlockCount

open Finset

theorem uniform_count (r : ℕ) (hr : 2 ≤ r) (a b E ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      ((PaperP1.ConnectedBlockLists.population G blocks).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨N₀, hN₀⟩ := PaperP1.RelativeBlockRelationsCount.uniform_count r 0 a b E ε ha hE hε
  refine ⟨N₀, ?_⟩
  intro N hN G blocks hvalues hdist
  let old : Fin 0 → ℕ := Fin.elim0
  let oldBlocks : Fin 0 → Finset ℕ := Fin.elim0
  have hc : ((PaperP1.RelativeBlockRelations.population G blocks ∅).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
    simpa using hN₀ N hN old oldBlocks G blocks hvalues (fun k ↦ Fin.elim0 k) hdist (fun k ↦ Fin.elim0 k)
  exact (show ((PaperP1.ConnectedBlockLists.population G blocks).card : ℝ) ≤
    (PaperP1.RelativeBlockRelations.population G blocks ∅).card by
      exact_mod_cast card_le_card (PaperP1.ConnectedBlockLists.population_subset_covered G blocks hr)).trans hc

end PaperP1.ConnectedBlockCount
