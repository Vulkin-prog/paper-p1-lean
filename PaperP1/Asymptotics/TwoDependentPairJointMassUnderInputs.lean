module

public import PaperP1.Model.TwoDependentPairSeeds
public import PaperP1.Asymptotics.NoSingletonJointMassUnderInputs

/-! # The actual union of any two disjoint dependent pairs has total joint seed mass exponent one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoDependentPairJointMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters 4, Hypotheses p (ε / 4) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ I ∈ TwoDependentPairSeeds.families G L, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := NoSingletonJointMassUnderInputs.uniform_range 4 C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  apply h N hN L hband 4 (by omega) (by omega) G hG (TwoDependentPairSeeds.families G L)
  intro I hI
  obtain ⟨hIG, hcard, hcore⟩ := TwoDependentPairSeeds.family_data G L I hI
  exact ⟨hIG, hcard, fun D hD ↦ CoreCanonicalComponents.block_card 2 L (by omega) I hcore D hD⟩

end PaperP1.TwoDependentPairJointMassUnderInputs
