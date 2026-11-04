module

public import PaperP1.Asymptotics.SharpConnectedChannelMassUnderInputs
public import PaperP1.Asymptotics.FiniteCompressedInteriorMass

/-! # One finite geometric bundle gives the sharp41/30 interior-channel triple mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpFiniteInteriorMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteCompressedInteriorMass

theorem uniform_channel (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b ε →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ConnectedCompressedTripleMassUnderInputs.mass N a b L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, h⟩ :=
    SharpConnectedChannelMassUnderInputs.uniform_mass a b ha hab hb2a hcop C ε hε
  exact ⟨⟨Ds, kg, ko, K⟩, fun hg ↦ h hg.sourceCover hg.ordinaryCover hg.sourceCurves hg.ordinaryCurves⟩

theorem uniform_mass (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → Parameters,
      (∀ ab, Hypotheses (p ab) ab.val.2 (ε / 2)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L Q ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have hch (ab : FiniteInteriorUnitEdges.channels Q) : ∃ p : Parameters, Hypotheses p ab.val.2 (ε / 2) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ConnectedCompressedTripleMassUnderInputs.mass N ab.val.1 ab.val.2 L ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    obtain ⟨ha, hab, hb2a, hcop, _haQ, _hbQ⟩ := FiniteInteriorUnitEdges.channel_data ab.property
    exact uniform_channel ab.val.1 ab.val.2 ha hab hb2a hcop C (ε / 2) (by positivity)
  choose p hp using hch
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption
    ((FiniteInteriorUnitEdges.channels Q).card : ℝ) (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  choose Nc _hNc hc using fun ab ↦ hp ab (hgeo ab)
  refine ⟨max 4 (max (univ.sup Nc) Nf), by omega, ?_⟩
  intro N hN L hcrit
  have hthreshold (ab : FiniteInteriorUnitEdges.channels Q) : Nc ab ≤ N :=
    (le_sup (f := Nc) (mem_univ ab)).trans (by omega)
  calc
    _ ≤ ∑ ab : FiniteInteriorUnitEdges.channels Q,
        ConnectedCompressedTripleMassUnderInputs.mass N ab.val.1 ab.val.2 L :=
      GraphStarWeights.sum_biUnion_le_nonneg univ _ _ (infiniteJointMoment_nonneg L)
    _ ≤ ∑ _ab : FiniteInteriorUnitEdges.channels Q, (N : ℝ) ^ (-41 / 30 + ε / 2) :=
      sum_le_sum fun ab _ ↦ hc ab N (hthreshold ab) L hcrit
    _ = ((FiniteInteriorUnitEdges.channels Q).card : ℝ) * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ _ := by
      simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)

end PaperP1.SharpFiniteInteriorMassUnderInputs
