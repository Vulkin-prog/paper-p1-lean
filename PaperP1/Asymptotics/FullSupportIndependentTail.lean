module

public import PaperP1.Model.IndependentFullSupportTail
public import PaperP1.Asymptotics.OriginalParticipatingTail
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The original-window clause of article15.8, with all exact heterogeneous marginals and one fixed cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullSupportIndependentTail

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem article_15_8_original (C v a ε : ℝ) (hv : 0 < v) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        IndependentFullSupportTail.mass G L s v ≤ (N : ℝ) ^ (-a + ε) := by
  let M := v * (2 * (2 : ℝ) ^ C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨s, hs, NP, _hNP, hp⟩ := OriginalParticipatingTail.subcritical_tail C M a ε hM ha hε
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  refine ⟨s, hs, max 10 (max NP NM), by omega, ?_⟩
  intro N hN L hband G hG
  apply hp N (by omega) L hband (fun x ↦ v * infiniteMarginal x L)
    (fun x ↦ mul_nonneg hv.le (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
  · intro x hx
    calc
      _ ≤ v * (2 * (2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hv.le
      _ = M / N := by dsimp [M]; ring
  · intro I hI
    obtain ⟨hIG, hsize, hfull⟩ := (IndependentFullSupportTail.mem_families G I L s).mp hI
    exact ⟨hIG.trans hG, hsize, IndependentFullSupportTail.witnesses L I hfull⟩

end PaperP1.FullSupportIndependentTail
