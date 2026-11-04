module

public import PaperP1.Asymptotics.MacroscopicLeadingPairGeometry
public import PaperP1.Asymptotics.MacroscopicSignedChannelComparison

/-! # Actual full leading positive and signed profiles

The complete enlarged leading sector retains local relations, incompatible
pairs, both orientations and the original separated source labels.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicActualLeadingProfiles

open Finset PaperP1.Arithmetic PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicFixedChannelComparison
  PaperP1.MacroscopicChannelPartition PaperP1.MacroscopicLeadingPairGeometry
  PaperP1.MacroscopicLeadingUnitSums PaperP1.UnsignedUnitFourierAggregate
  PaperP1.PrivateUnitCovariance PaperP1.ChannelSumIdentity

def positive (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ := ∑ xy ∈ leading M δ L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)

def signed (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ := ∑ xy ∈ leading M δ L, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L

theorem doubled_sum_error (E : Finset (ℕ × ℕ)) (f g : ℕ × ℕ → ℝ) :
    |2 * (∑ xy ∈ E, f xy) - 2 * (∑ xy ∈ E, g xy)| ≤ 2 * ∑ xy ∈ E, |f xy - g xy| := by
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem uniform_comparison (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |positive M δ L - unsignedTotal M δ L| ≤ (M : ℝ) ^ (1 + ε) ∧
      |signed M δ L - signedTotal M δ L| ≤ (M : ℝ) ^ (1 + ε) := by
  obtain ⟨MG, hG⟩ := uniform_separation C δ hδ
  obtain ⟨MS, hS⟩ := uniform_symmetric_sum C δ hδ
  obtain ⟨MP, hP⟩ := uniform_power_error C δ hδ 2 2 (by omega) (ε / 2) (by positivity)
  obtain ⟨MA, hA⟩ := PaperP1.MacroscopicSignedChannelComparison.height_two C δ hδ (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MG (max MS (max MP (max MA MF))), ?_⟩
  intro M hM L hcrit
  let E := channelPairs M δ 1 2 L
  have hne : ∀ xy ∈ E, xy.1 ≠ xy.2 := by
    intro xy hxy
    have hh := hG M (by omega) L hcrit xy hxy
    omega
  have hp := hP M (by omega) L 1 2 hcrit (by omega) (by omega) (by norm_num)
    (by omega) (by omega) E (Subset.refl _)
  norm_num only [Nat.cast_ofNat, show (1 : ℝ) / 2 + 1 / (2 : ℝ) + ε / 2 = 1 + ε / 2 by ring] at hp
  have ha := hA M (by omega) L hcrit E (Subset.refl _) hne
  obtain ⟨huRat, hsRat⟩ := rational_forward_sums (by omega : 2 ≤ M) hδ (L := L)
  have huR : unsignedTotal M δ L = 2 * ∑ xy ∈ E, unitWeight 1 2 xy.1 xy.2 L := by
    unfold unsignedTotal
    rw [huRat]
  have hsR : signedTotal M δ L = 2 * ∑ xy ∈ E, signedUnitSum 1 2 xy.1 xy.2 L := by
    unfold signedTotal
    rw [hsRat]
  have hsum := (hS M (by omega) L hcrit).2.2
  have huSum : positive M δ L = 2 * ∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1) := by
    apply hsum
    intro xy
    change (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 = (2 ^ pairLoss xy.2 xy.1 L : ℝ) - 1
    rw [pairLoss_comm xy.1 xy.2 L]
  have hsSum : signed M δ L = 2 * ∑ xy ∈ E, PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L := by
    apply hsum
    intro xy
    exact PaperP1.ActualAffinePairWeight.weight_comm xy.1 xy.2 L
  have hpos : |positive M δ L - unsignedTotal M δ L| ≤ 2 * (M : ℝ) ^ (1 + ε / 2) := by
    rw [huSum, huR]
    have hh := doubled_sum_error E (fun xy ↦ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)
      (fun xy ↦ unitWeight 1 2 xy.1 xy.2 L)
    have heq : (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 - unitWeight 1 2 xy.1 xy.2 L|) =
        ∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units 1 2 xy.1 xy.2 L).card - 1)| := by
      apply sum_congr rfl
      intro xy _
      unfold unitWeight
      congr 1
      ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2))
  have hsign : |signed M δ L - signedTotal M δ L| ≤ 2 * (M : ℝ) ^ (1 + ε / 2) := by
    rw [hsSum, hsR]
    exact (doubled_sum_error E (fun xy ↦ PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L)
      (fun xy ↦ signedUnitSum 1 2 xy.1 xy.2 L)).trans (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2))
  have hf : 2 * (M : ℝ) ^ (1 + ε / 2) ≤ (M : ℝ) ^ (1 + ε) := by
    simpa only [show (1 : ℝ) + ε / 2 + ε / 2 = 1 + ε by ring] using hF M (by omega)
  exact ⟨hpos.trans hf, hsign.trans hf⟩

theorem uniform_main_terms (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |positive M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ)| ≤ (M : ℝ) ^ (1 + ε) ∧
      |signed M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (ChannelSumIdentity.signed L 1 2 : ℤ)| ≤
        (M : ℝ) ^ (1 + ε) := by
  obtain ⟨MC, hC⟩ := uniform_comparison C δ hδ (ε / 2) (by positivity)
  obtain ⟨MU, hU⟩ := uniform_power_errors C δ hδ hδ1 (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MC (max MU MF), ?_⟩
  intro M hM L hcrit
  obtain ⟨hcp, hcs⟩ := hC M (by omega) L hcrit
  obtain ⟨hup, hus⟩ := hU M (by omega) L hcrit
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ (1 / 2 + ε / 2) ≤ (M : ℝ) ^ (1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hf : 2 * (M : ℝ) ^ (1 + ε / 2) ≤ (M : ℝ) ^ (1 + ε) := by
    simpa only [show (1 : ℝ) + ε / 2 + ε / 2 = 1 + ε by ring] using hF M (by omega)
  constructor
  · exact (abs_sub_le (positive M δ L) (unsignedTotal M δ L)
      (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ))).trans
        ((by linarith only [hcp, hup.trans hpower] : _ ≤ 2 * (M : ℝ) ^ (1 + ε / 2)).trans hf)
  · exact (abs_sub_le (signed M δ L) (signedTotal M δ L)
      (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (ChannelSumIdentity.signed L 1 2 : ℤ))).trans
        ((by linarith only [hcs, hus.trans hpower] : _ ≤ 2 * (M : ℝ) ^ (1 + ε / 2)).trans hf)

end PaperP1.MacroscopicActualLeadingProfiles
