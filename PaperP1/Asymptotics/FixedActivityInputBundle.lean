module

public import PaperP1.Asymptotics.FixedMomentInputs
public import PaperP1.Asymptotics.FullFixedActivityUnderInputs

/-! # The existing fixed-moment geometric bundle also supplies the full higher activity bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedActivityInputBundle

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FixedMomentInputs

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 4) := by
  obtain ⟨pc, pi, pd, pp, pq, h⟩ := FullFixedActivityUnderInputs.uniform_range R C (ε / 4) (by positivity)
  refine ⟨⟨pc, pi, pd, pp, pq⟩, ?_⟩
  intro hp
  have hC : (ε / 4) / 32 = ε / 128 := by ring
  have hI : (ε / 4) / 128 = ε / 512 := by ring
  have hP : (ε / 4) / 131072 = ε / 524288 := by ring
  have hD : (ε / 4) / 8 = ε / 32 := by ring
  exact h (by simpa only [hC] using hp.compatible) (by simpa only [hI] using hp.incompatible)
    (by simpa only [hP] using hp.pair) (by simpa only [hD] using hp.nonconnected)
    (by simpa only [hD] using hp.nonconnectedPair)

end PaperP1.FixedActivityInputBundle
