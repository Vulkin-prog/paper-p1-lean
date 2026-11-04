module

public import PaperP1.Asymptotics.DyadicPositiveEquivalents
public import PaperP1.Asymptotics.MacroscopicRationalProfile

/-! # Companion T21.1, on the original ordered pair domains

The conclusion contains all dyadic and macroscopic assertions. The
rational profiles are the global ratio-fiber codes; support on alignment
was proved, rather than imposed in their definitions. No arithmetic
profile or external counting premise is accepted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompanionT21Profiles

theorem macroscopic_positive_reference_eval (M : ℕ) {k r : ℕ}
    (hk : 1 ≤ k) (hr : r < 2) :
    (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain (2 * k + r - 1) =
      ((2 : ℝ) + r) / 4 * M * ((2 * k + r : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  rw [PaperP1.OneTwoChannelPhase.positiveMain_eval hk hr]
  ring

theorem macroscopic_signed_reference_eval (M m s : ℕ) (hs : s < 2) :
    (M : ℝ) * PaperP1.OneTwoChannelPhase.signedMain (2 * m + s) =
      ((s : ℝ) + 1) / 4 * M * ((2 * m + s : ℕ) : ℝ) * (2 : ℝ) ^ m := by
  rw [PaperP1.OneTwoChannelPhase.signedMain_eval hs]
  ring

theorem macroscopic_positive_uniform (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L ∧
      |PaperP1.MacroscopicRationalProfile.profile M δ L /
        ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1| ≤ η ∧
      |PaperP1.MacroscopicActualProfiles.positive M δ L /
        ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1| ≤ η := by
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicRationalProfile.uniform_ratio C δ hδ hδ1 η hη
  obtain ⟨MA, hA⟩ := PaperP1.MacroscopicActualProfileEquivalents.uniform_ratio C δ hδ hδ1 η hη
  refine ⟨max MR MA, ?_⟩
  intro M hM L hcrit
  obtain ⟨hp, hr⟩ := hR M (by omega) L hcrit
  exact ⟨hp, hr, (hA M (by omega) L hcrit).2.2.1⟩

structure Conclusion (C : ℝ) : Prop where
  dyadic_equivalent : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < PaperP1.DyadicPositiveEquivalents.reference N L ∧
    |PaperP1.DyadicPositiveProfiles.rational N L / PaperP1.DyadicPositiveEquivalents.reference N L - 1| ≤ η ∧
    |PaperP1.DyadicPositiveProfiles.positive N L / PaperP1.DyadicPositiveEquivalents.reference N L - 1| ≤ η
  dyadic_comparison : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 ≤ PaperP1.DyadicPositiveProfiles.positive N L - PaperP1.DyadicPositiveProfiles.rational N L ∧
    PaperP1.DyadicPositiveProfiles.positive N L - PaperP1.DyadicPositiveProfiles.rational N L ≤ (N : ℝ) ^ (5 / 4 + ε)
  macroscopic_positive : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ η : ℝ, 0 < η →
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
    0 < (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L ∧
    |PaperP1.MacroscopicRationalProfile.profile M δ L /
      ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1| ≤ η ∧
    |PaperP1.MacroscopicActualProfiles.positive M δ L /
      ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1| ≤ η
  macroscopic_comparison : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ ε : ℝ, 0 < ε →
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
    0 ≤ PaperP1.MacroscopicActualProfiles.positive M δ L - PaperP1.MacroscopicRationalProfile.profile M δ L ∧
    PaperP1.MacroscopicActualProfiles.positive M δ L - PaperP1.MacroscopicRationalProfile.profile M δ L ≤
      (M : ℝ) ^ (4 / 3 + ε)
  macroscopic_signed_formula : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ ε : ℝ, 0 < ε →
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
    |PaperP1.MacroscopicActualProfiles.signed M δ L -
      ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (PaperP1.ChannelSumIdentity.signed L 1 2 : ℤ)| ≤
      (M : ℝ) ^ (4 / 3 + ε)
  signed_channel_formula : ∀ m s : ℕ, 1 ≤ m → s < 2 →
    PaperP1.ChannelSumIdentity.signed (2 * m + s) 1 2 = (2 : ℤ) ^ (m - 1) *
      (((s : ℤ) + 1) * m + (s : ℤ) ^ 2 + s + 4) - 3 * (2 * m + s : ℕ) + 1
  macroscopic_signed_equivalent : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ η : ℝ, 0 < η →
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
    |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
    0 < (M : ℝ) * PaperP1.OneTwoChannelPhase.signedMain L ∧
    |PaperP1.MacroscopicActualProfiles.signed M δ L /
      ((M : ℝ) * PaperP1.OneTwoChannelPhase.signedMain L) - 1| ≤ η

theorem companion_T21_1 (C : ℝ) : Conclusion C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun η hη ↦ PaperP1.DyadicPositiveEquivalents.uniform_ratio C η hη
  · exact fun ε hε ↦ PaperP1.DyadicPositiveProfiles.uniform_comparison C ε hε
  · exact fun δ hδ hδ1 η hη ↦ macroscopic_positive_uniform C δ hδ hδ1 η hη
  · exact fun δ hδ hδ1 ε hε ↦ PaperP1.MacroscopicRationalProfile.uniform_comparison C δ hδ hδ1 ε hε
  · intro δ hδ hδ1 ε hε
    obtain ⟨M₀, h⟩ := PaperP1.MacroscopicActualProfiles.uniform_main_terms C δ hδ hδ1 ε hε
    exact ⟨M₀, fun M hM L hcrit ↦ (h M hM L hcrit).2⟩
  · exact fun _m _s hm hs ↦ PaperP1.OneTwoChannelParity.signed_formula hm hs
  · intro δ hδ hδ1 η hη
    obtain ⟨M₀, h⟩ := PaperP1.MacroscopicActualProfileEquivalents.uniform_ratio C δ hδ hδ1 η hη
    refine ⟨M₀, ?_⟩
    intro M hM L hcrit
    have hh := h M hM L hcrit
    exact ⟨hh.2.1, hh.2.2.2⟩

end PaperP1.CompanionT21Profiles
