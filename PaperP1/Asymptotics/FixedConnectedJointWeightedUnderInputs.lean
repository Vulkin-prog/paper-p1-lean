module

public import PaperP1.Asymptotics.NoSingletonJointMassUnderInputs
public import PaperP1.Model.CoreCanonicalComponents
public import PaperP1.Model.OriginalTwoAnchorWitnesses

/-! # Full actual connected joint mass has weighted rate1 over every prescribed bounded order range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedConnectedJointWeightedUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (R : ℕ) (u C ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p (ε / 8) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ R ∧ Connected L I) →
      (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := NoSingletonJointMassUnderInputs.uniform_weighted R u C ε hu hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG F hF
  apply h N hN L hband G hG F
  intro I hI
  obtain ⟨hIG, hthree, hcap, hconn⟩ := hF I hI
  have hcore := OriginalTwoAnchorWitnesses.connected_core L I (by omega) hconn
  exact ⟨hIG, hthree, hcap, fun D hD ↦ CoreCanonicalComponents.block_card 2 L le_rfl I hcore D hD⟩

end PaperP1.FixedConnectedJointWeightedUnderInputs
