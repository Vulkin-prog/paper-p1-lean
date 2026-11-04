module

public import PaperP1.Model.RawDependencePairs
public import PaperP1.Asymptotics.RawTwoWindowHostCount

/-! # Uniform unconditional count of actual raw-dependence exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawDependenceCount

theorem uniform_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, 1 ≤ B →
      (B : ℝ) ≤ D * Real.log N → ∀ M : ℕ, 2 * N + B ≤ M →
      ((PaperP1.RawDependencePairs.badPairs M N B).card : ℝ) ≤
        (N : ℝ) ^ (3 / 2 + ε : ℝ) := by
  obtain ⟨NH, hH⟩ := PaperP1.RawTwoWindowHostCount.uniform_bound D hD ε hε
  refine ⟨max NH 2, ?_⟩
  intro N hN B hB hlog M hM
  have hc : ((PaperP1.RawDependencePairs.badPairs M N B).card : ℝ) ≤
      (PaperP1.RawTwoWindowHosts.hosts N B).card := by
    exact_mod_cast PaperP1.RawDependencePairs.card_le_hosts (by omega) hM
  exact hc.trans (hH N (by omega) B hB hlog)

theorem uniform_rectangular_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, 1 ≤ B →
      (B : ℝ) ≤ D * Real.log N → ∀ M S T : ℕ, 2 * N + B ≤ M → S ≤ B → T ≤ B →
      ((PaperP1.RawDependencePairs.rectangularBadPairs M N S T).card : ℝ) ≤
        (N : ℝ) ^ (3 / 2 + ε : ℝ) := by
  obtain ⟨NH, hH⟩ := uniform_bound D hD ε hε
  refine ⟨NH, ?_⟩
  intro N hN B hB hlog M S T hM hS hT
  have hc : ((PaperP1.RawDependencePairs.rectangularBadPairs M N S T).card : ℝ) ≤
      (PaperP1.RawDependencePairs.badPairs M N B).card := by
    exact_mod_cast Finset.card_le_card (PaperP1.RawDependencePairs.rectangular_subset
      (M := M) (N := N) hS hT)
  exact hc.trans (hH N hN B hB hlog M hM)

end PaperP1.RawDependenceCount
