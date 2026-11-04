module

public import PaperP1.Asymptotics.MacroscopicActualLeadingProfiles
public import PaperP1.Asymptotics.MacroscopicActualSignedMass

/-! # Actual complete aligned positive and signed macroscopic profiles

The exact disjoint sector partition and the actual leading comparison
are assembled on the original ordered separated domain. Every arithmetic
estimate is proved internally, with no profile bound supplied as input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicActualProfiles

open Finset PaperP1.Arithmetic PaperP1.NormalizedPairRankLoss
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicChannelPartition
  PaperP1.ChannelSumIdentity

def positive (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ := ∑ xy ∈ aligned M δ L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)

def signed (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ := ∑ xy ∈ aligned M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L

theorem uniform_main_terms (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |positive M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ)| ≤ (M : ℝ) ^ (4 / 3 + ε) ∧
      |signed M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (ChannelSumIdentity.signed L 1 2 : ℤ)| ≤
        (M : ℝ) ^ (4 / 3 + ε) := by
  obtain ⟨MT, hT⟩ := PaperP1.MacroscopicActualLeadingProfiles.uniform_main_terms C δ hδ hδ1 (ε / 2) (by positivity)
  obtain ⟨MP, hP⟩ := uniform_sum C δ hδ
  obtain ⟨ML, hL⟩ := PaperP1.MacroscopicSeparatedHeightOne.uniform_weights C δ hδ (ε / 2) (by positivity)
  obtain ⟨MH, hH⟩ := PaperP1.MacroscopicHighRelationMass.high_height_three C δ hδ (ε / 2) (by positivity)
  obtain ⟨MSL, hSL⟩ := PaperP1.MacroscopicActualSignedMass.uniform_height_one C δ hδ (ε / 2) (by positivity)
  obtain ⟨MSH, hSH⟩ := PaperP1.MacroscopicActualSignedMass.high_height_three C δ hδ (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 3 (4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MT (max MP (max ML (max MH (max MSL (max MSH MF))))), ?_⟩
  intro M hM L hcrit
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ (1 + ε / 2) ≤ (M : ℝ) ^ (4 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  obtain ⟨htp, hts⟩ := hT M (by omega) L hcrit
  have hlowP := (hL M (by omega) L hcrit).1
  have hhighP : (∑ xy ∈ high M δ L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) ≤ (M : ℝ) ^ (4 / 3 + ε / 2) := by
    have hsub : high M δ L ⊆ PaperP1.MacroscopicHighRelationMass.highPairs M δ L 3 := filter_subset _ _
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun xy _ _ ↦
      sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))).trans (hH M (by omega) L hcrit).1
  have hlowS := hSL M (by omega) L hcrit
  have hhighS : (∑ xy ∈ high M δ L, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L|) ≤
      (M : ℝ) ^ (4 / 3 + ε / 2) := by
    have hsub : high M δ L ⊆ PaperP1.MacroscopicHighRelationMass.highPairs M δ L 3 := filter_subset _ _
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ abs_nonneg _)).trans (hSH M (by omega) L hcrit)
  have hpSum := hP M (by omega) L hcrit (fun xy ↦ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)
  have hsSum := hP M (by omega) L hcrit (fun xy ↦ PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L)
  have hdP : |positive M δ L - PaperP1.MacroscopicActualLeadingProfiles.positive M δ L| ≤
      2 * (M : ℝ) ^ (4 / 3 + ε / 2) := by
    unfold positive PaperP1.MacroscopicActualLeadingProfiles.positive
    rw [hpSum]
    have hzlow : 0 ≤ ∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L,
        ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1) :=
      sum_nonneg fun _ _ ↦ sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hzhigh : 0 ≤ ∑ xy ∈ high M δ L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1) :=
      sum_nonneg fun _ _ ↦ sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    rw [abs_of_nonneg (by linarith only [hzlow, hzhigh])]
    linarith only [hlowP.trans hpower, hhighP]
  have hdS : |signed M δ L - PaperP1.MacroscopicActualLeadingProfiles.signed M δ L| ≤
      2 * (M : ℝ) ^ (4 / 3 + ε / 2) := by
    unfold signed PaperP1.MacroscopicActualLeadingProfiles.signed
    rw [hsSum]
    have heq : (∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) +
        (∑ xy ∈ leading M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) +
        (∑ xy ∈ high M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) -
        (∑ xy ∈ leading M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) =
        (∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) +
        (∑ xy ∈ high M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by
      have hl := (abs_sum_le_sum_abs _ _).trans hlowS
      have hh := (abs_sum_le_sum_abs _ _).trans hhighS
      linarith only [hl.trans hpower, hh])
  have hf : 3 * (M : ℝ) ^ (4 / 3 + ε / 2) ≤ (M : ℝ) ^ (4 / 3 + ε) := by
    simpa only [show (4 : ℝ) / 3 + ε / 2 + ε / 2 = 4 / 3 + ε by ring] using hF M (by omega)
  constructor
  · exact (abs_sub_le (positive M δ L) (PaperP1.MacroscopicActualLeadingProfiles.positive M δ L)
      (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ))).trans
        ((by linarith only [hdP, htp.trans hpower] : _ ≤ 3 * (M : ℝ) ^ (4 / 3 + ε / 2)).trans hf)
  · exact (abs_sub_le (signed M δ L) (PaperP1.MacroscopicActualLeadingProfiles.signed M δ L)
      (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (ChannelSumIdentity.signed L 1 2 : ℤ))).trans
        ((by linarith only [hdS, hts.trans hpower] : _ ≤ 3 * (M : ℝ) ^ (4 / 3 + ε / 2)).trans hf)

end PaperP1.MacroscopicActualProfiles
