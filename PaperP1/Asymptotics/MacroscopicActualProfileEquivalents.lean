module

public import PaperP1.Asymptotics.MacroscopicActualProfiles
public import PaperP1.Asymptotics.MacroscopicPhaseScale

/-! # Complete actual macroscopic aligned profiles have the printed equivalents

Both phases use their own actual moving residue. The threshold precedes
every critical length. The lower endpoint and full arithmetic remainder
are proved negligible relative to the positive leading terms.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicActualProfileEquivalents

open PaperP1.OneTwoChannelPhase PaperP1.MacroscopicActualProfiles

theorem relative_transfer {M d P U F η : ℝ} (hM : 0 ≤ M) (hd : 0 ≤ d) (hF : 0 ≤ F)
    (hlo : 0 ≤ M - d) (hhi : M - d ≤ M) (hend : d ≤ (η / 3) * M)
    (hchannel : |U - F| ≤ (η / 3) * F)
    (herror : |P - (M - d) * U| ≤ (η / 3) * M * F) : |P - M * F| ≤ η * M * F := by
  have hprod : (M - d) * |U - F| ≤ M * ((η / 3) * F) := mul_le_mul hhi hchannel (abs_nonneg _) hM
  have hendprod := mul_le_mul_of_nonneg_right hend hF
  have hmid : |(M - d) * U - M * F| ≤ 2 * ((η / 3) * M * F) := by
    have heq : (M - d) * U - M * F = (M - d) * (U - F) - d * F := by ring
    rw [heq]
    have ht := abs_sub_le ((M - d) * (U - F)) 0 (d * F)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hlo, abs_of_nonneg hd, abs_of_nonneg hF] at ht
    nlinarith only [ht, hprod, hendprod]
  have ht := abs_sub_le P ((M - d) * U) (M * F)
  nlinarith only [ht, hmid, herror]

theorem uniform_relative (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |positive M δ L - (M : ℝ) * positiveMain L| ≤ η * M * positiveMain L ∧
      |signed M δ L - (M : ℝ) * signedMain L| ≤ η * M * signedMain L := by
  obtain ⟨MA, hA⟩ := uniform_main_terms C δ hδ hδ1 (1 / 12) (by norm_num)
  obtain ⟨MC, hC⟩ := PaperP1.OneTwoChannelPhase.uniform_critical_relative C (η / 3) (by positivity)
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicPhaseScale.power_error_negligible C (17 / 12) (η / 3) (by norm_num) (by positivity)
  obtain ⟨MD, hD⟩ := PaperP1.MacroscopicPhaseScale.lower_endpoint_small δ (η / 3) hδ1 (by positivity)
  refine ⟨max MA (max MC (max MR MD)), ?_⟩
  intro M hM L hcrit
  obtain ⟨haP, haS⟩ := hA M (by omega) L hcrit
  norm_num only [show (4 : ℝ) / 3 + 1 / 12 = 17 / 12 by norm_num] at haP haS
  obtain ⟨hcP, hcS⟩ := hC M (by omega) L hcrit
  obtain ⟨hrP, hrS⟩ := hR M (by omega) L hcrit
  obtain ⟨hdlo, hdhi, hdsmall⟩ := hD M (by omega)
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hd : (0 : ℝ) ≤ 2 * (M : ℝ) ^ δ := by positivity
  have hp : 0 ≤ positiveMain L := (positiveMain_pos L).le
  have hs : 0 ≤ signedMain L := by unfold signedMain; positivity
  exact ⟨relative_transfer hm hd hp hdlo hdhi hdsmall hcP (haP.trans hrP),
    relative_transfer hm hd hs hdlo hdhi hdsmall hcS (haS.trans hrS)⟩

theorem uniform_ratio (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < (M : ℝ) * positiveMain L ∧ 0 < (M : ℝ) * signedMain L ∧
      |positive M δ L / ((M : ℝ) * positiveMain L) - 1| ≤ η ∧
      |signed M δ L / ((M : ℝ) * signedMain L) - 1| ≤ η := by
  obtain ⟨MR, hR⟩ := uniform_relative C δ hδ hδ1 η hη
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MR MG, ?_⟩
  intro M hM L hcrit
  obtain ⟨hp, hs⟩ := hR M (by omega) L hcrit
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hpos := mul_pos hm (positiveMain_pos L)
  have hsign := mul_pos hm (signedMain_pos hL)
  refine ⟨hpos, hsign, ?_, ?_⟩
  · have heq : positive M δ L / ((M : ℝ) * positiveMain L) - 1 =
        (positive M δ L - (M : ℝ) * positiveMain L) / ((M : ℝ) * positiveMain L) := by field_simp [hm.ne', (positiveMain_pos L).ne']
    rw [heq, abs_div, abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_assoc] using hp)
  · have heq : signed M δ L / ((M : ℝ) * signedMain L) - 1 =
        (signed M δ L - (M : ℝ) * signedMain L) / ((M : ℝ) * signedMain L) := by field_simp [hm.ne', (signedMain_pos hL).ne']
    rw [heq, abs_div, abs_of_pos hsign]
    exact (div_le_iff₀ hsign).mpr (by simpa only [mul_assoc] using hs)

end PaperP1.MacroscopicActualProfileEquivalents
