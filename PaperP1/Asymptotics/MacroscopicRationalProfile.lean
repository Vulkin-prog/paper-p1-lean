module

public import PaperP1.Asymptotics.MacroscopicRationalCodeGeometry
public import PaperP1.Asymptotics.MacroscopicActualProfileEquivalents

/-! # The global rational macroscopic profile on all original separated pairs

The code is defined from all actual ratio fibers. Its support is proved
aligned and its leading sector equals the literal rational-unit total.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicRationalProfile

open Finset PaperP1.Arithmetic PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicHighRelationMass
  PaperP1.MacroscopicChannelPartition PaperP1.MacroscopicFixedChannelComparison
  PaperP1.UnsignedUnitFourierAggregate PaperP1.MacroscopicLeadingUnitSums

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (M : ℕ) (δ : ℝ) (L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ L < Nat.dist xy.1 xy.2

def profile (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ :=
  ∑ xy ∈ pairs M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L

theorem aligned_subset (M L : ℕ) (δ : ℝ) : aligned M δ L ⊆ pairs M δ L := by
  intro xy hxy
  obtain ⟨hh, hsep⟩ := mem_filter.mp hxy
  obtain ⟨ab, _hab, hpair⟩ := mem_biUnion.mp hh
  exact mem_filter.mpr ⟨(mem_filter.mp hpair).1, hsep⟩

theorem uniform_support_eq (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      profile M δ L = ∑ xy ∈ aligned M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_off_channel C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  symm
  apply sum_subset (aligned_subset M L δ)
  intro xy hxy hn
  obtain ⟨hblock, hsep⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hnot : xy ∉ highPairs M δ L 1 := fun hh ↦ hn (mem_filter.mpr ⟨hh, hsep⟩)
  exact (h M hM L hcrit xy.1 hx xy.2 hy hnot).2

theorem uniform_leading_eq (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ leading M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L) = unsignedTotal M δ L := by
  obtain ⟨MC, hC⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_channel C δ hδ
  obtain ⟨MS, hS⟩ := PaperP1.MacroscopicLeadingPairGeometry.uniform_symmetric_sum C δ hδ
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MC (max MS MG), ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hB : 2 ≤ (L + 1) ^ 3 := (by omega : 2 ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hforward : ∀ xy ∈ channelPairs M δ 1 2 L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L = unitWeight 1 2 xy.1 xy.2 L := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have heq := (hC M (by omega) L hcrit xy.1 hx xy.2 hy 1 2 (by omega) (by omega) (by norm_num) (by omega) hB hg).1
    rw [PaperP1.RationalUnitCode.weight, heq]
    rfl
  have hreverse : ∀ xy ∈ channelPairs M δ 2 1 L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L = unitWeight 1 2 xy.2 xy.1 L := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have heq := (hC M (by omega) L hcrit xy.1 hx xy.2 hy 2 1 (by omega) (by omega) (by norm_num) hB (by omega) hg).1
    have hcard := units_card_swap (x := xy.1) (y := xy.2) (L := L) (by omega : 0 < 2) (by omega : 0 < 1)
      (by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega)
      (by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega)
    rw [PaperP1.RationalUnitCode.weight, heq, hcard]
    rfl
  obtain ⟨heq, hdis, _hsum⟩ := hS M (by omega) L hcrit
  rw [heq, sum_union hdis]
  have hf := sum_congr rfl hforward
  have hr := sum_congr rfl hreverse
  rw [hf, hr]
  have hswap : (∑ xy ∈ channelPairs M δ 2 1 L, unitWeight 1 2 xy.2 xy.1 L) =
      ∑ xy ∈ channelPairs M δ 1 2 L, unitWeight 1 2 xy.1 xy.2 L := by
    rw [← channel_swap M 1 2 L δ, sum_image]
    · rfl
    · intro xy _ uv _ hh
      have hk := congrArg Prod.swap hh
      simpa only [Prod.swap_swap] using hk
  rw [hswap, (PaperP1.MacroscopicLeadingPairGeometry.rational_forward_sums (by omega : 2 ≤ M) hδ (L := L)).1]
  unfold unsignedTotal
  ring

theorem uniform_domination (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 ≤ profile M δ L ∧ profile M δ L ≤ PaperP1.MacroscopicActualProfiles.positive M δ L := by
  obtain ⟨MS, hS⟩ := uniform_support_eq C δ hδ
  obtain ⟨MB, hB⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_aligned_bound C δ hδ
  refine ⟨max MS MB, ?_⟩
  intro M hM L hcrit
  constructor
  · exact sum_nonneg fun xy _ ↦ PaperP1.RationalUnitCode.weight_nonneg xy.1 xy.2 L
  · rw [hS M (by omega) L hcrit]
    exact sum_le_sum (hB M (by omega) L hcrit)


theorem uniform_rational_remainder (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 ≤ profile M δ L - unsignedTotal M δ L ∧
      profile M δ L - unsignedTotal M δ L ≤ (M : ℝ) ^ (4 / 3 + ε) := by
  obtain ⟨MS, hS⟩ := uniform_support_eq C δ hδ
  obtain ⟨MP, hP⟩ := uniform_sum C δ hδ
  obtain ⟨ML, hL⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_low_zero C δ hδ
  obtain ⟨MT, hT⟩ := uniform_leading_eq C δ hδ
  obtain ⟨MB, hB⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_aligned_bound C δ hδ
  obtain ⟨MH, hH⟩ := PaperP1.MacroscopicHighRelationMass.high_height_three C δ hδ ε hε
  refine ⟨max MS (max MP (max ML (max MT (max MB MH)))), ?_⟩
  intro M hM L hcrit
  have hlow : (∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L) = 0 := sum_eq_zero (hL M (by omega) L hcrit)
  have hsplit : profile M δ L = unsignedTotal M δ L +
      ∑ xy ∈ high M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L := by
    rw [hS M (by omega) L hcrit, hP M (by omega) L hcrit, hlow, zero_add, hT M (by omega) L hcrit]
  have hnonneg : 0 ≤ ∑ xy ∈ high M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L :=
    sum_nonneg fun xy _ ↦ PaperP1.RationalUnitCode.weight_nonneg xy.1 xy.2 L
  have hcap : (∑ xy ∈ high M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L) ≤ (M : ℝ) ^ (4 / 3 + ε) := by
    have hpoint : ∀ xy ∈ high M δ L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L ≤
        (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 :=
      fun xy hxy ↦ hB M (by omega) L hcrit xy (high_subset M L δ hxy)
    have hsub : high M δ L ⊆ highPairs M δ L 3 := filter_subset _ _
    exact (sum_le_sum hpoint).trans ((sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ ↦ sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))).trans (hH M (by omega) L hcrit).1)
  rw [hsplit]
  exact ⟨by linarith only [hnonneg], by linarith only [hcap]⟩

theorem uniform_main_term (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |profile M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (PaperP1.ChannelSumIdentity.unsigned L 1 2 : ℤ)| ≤
        (M : ℝ) ^ (4 / 3 + ε) := by
  obtain ⟨MR, hR⟩ := uniform_rational_remainder C δ hδ (ε / 2) (by positivity)
  obtain ⟨MU, hU⟩ := uniform_power_errors C δ hδ hδ1 (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MR (max MU MF), ?_⟩
  intro M hM L hcrit
  obtain ⟨hr0, hr⟩ := hR M (by omega) L hcrit
  have hu := (hU M (by omega) L hcrit).1
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpower : (M : ℝ) ^ (1 / 2 + ε / 2) ≤ (M : ℝ) ^ (4 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hf : 2 * (M : ℝ) ^ (4 / 3 + ε / 2) ≤ (M : ℝ) ^ (4 / 3 + ε) := by
    simpa only [show (4 : ℝ) / 3 + ε / 2 + ε / 2 = 4 / 3 + ε by ring] using hF M (by omega)
  have ht := abs_sub_le (profile M δ L) (unsignedTotal M δ L)
    (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (PaperP1.ChannelSumIdentity.unsigned L 1 2 : ℤ))
  rw [abs_of_nonneg hr0] at ht
  exact ht.trans ((by linarith only [hr, hu.trans hpower] : _ ≤ 2 * (M : ℝ) ^ (4 / 3 + ε / 2)).trans hf)

theorem uniform_comparison (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 ≤ PaperP1.MacroscopicActualProfiles.positive M δ L - profile M δ L ∧
      PaperP1.MacroscopicActualProfiles.positive M δ L - profile M δ L ≤ (M : ℝ) ^ (4 / 3 + ε) := by
  obtain ⟨MD, hD⟩ := uniform_domination C δ hδ
  obtain ⟨MA, hA⟩ := PaperP1.MacroscopicActualProfiles.uniform_main_terms C δ hδ hδ1 (ε / 2) (by positivity)
  obtain ⟨MR, hR⟩ := uniform_main_term C δ hδ hδ1 (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MD (max MA (max MR MF)), ?_⟩
  intro M hM L hcrit
  have hd : 0 ≤ PaperP1.MacroscopicActualProfiles.positive M δ L - profile M δ L :=
    sub_nonneg.mpr (hD M (by omega) L hcrit).2
  have ha := (hA M (by omega) L hcrit).1
  have hr := hR M (by omega) L hcrit
  have hf : 2 * (M : ℝ) ^ (4 / 3 + ε / 2) ≤ (M : ℝ) ^ (4 / 3 + ε) := by
    simpa only [show (4 : ℝ) / 3 + ε / 2 + ε / 2 = 4 / 3 + ε by ring] using hF M (by omega)
  have ht := abs_sub_le (PaperP1.MacroscopicActualProfiles.positive M δ L)
    (((M : ℝ) - 2 * (M : ℝ) ^ δ) * (PaperP1.ChannelSumIdentity.unsigned L 1 2 : ℤ)) (profile M δ L)
  rw [abs_of_nonneg hd, abs_sub_comm _ (profile M δ L)] at ht
  exact ⟨hd, ht.trans ((by linarith only [ha, hr] : _ ≤ 2 * (M : ℝ) ^ (4 / 3 + ε / 2)).trans hf)⟩


theorem uniform_relative (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |profile M δ L - (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L| ≤
        η * M * PaperP1.OneTwoChannelPhase.positiveMain L := by
  obtain ⟨MC, hC⟩ := uniform_comparison C δ hδ hδ1 (1 / 12) (by norm_num)
  obtain ⟨MA, hA⟩ := PaperP1.MacroscopicActualProfileEquivalents.uniform_relative C δ hδ hδ1 (η / 2) (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPhaseScale.power_error_negligible C (17 / 12) (η / 2) (by norm_num) (by positivity)
  refine ⟨max MC (max MA MP), ?_⟩
  intro M hM L hcrit
  obtain ⟨hc0, hc⟩ := hC M (by omega) L hcrit
  norm_num only [show (4 : ℝ) / 3 + 1 / 12 = 17 / 12 by norm_num] at hc
  have hp := (hP M (by omega) L hcrit).1
  have ha := (hA M (by omega) L hcrit).1
  have hdiff : |profile M δ L - PaperP1.MacroscopicActualProfiles.positive M δ L| ≤
      (η / 2) * M * PaperP1.OneTwoChannelPhase.positiveMain L := by
    rw [abs_sub_comm, abs_of_nonneg hc0]
    exact hc.trans hp
  have ht := abs_sub_le (profile M δ L) (PaperP1.MacroscopicActualProfiles.positive M δ L)
    ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L)
  nlinarith only [ht, hdiff, ha]

theorem uniform_ratio (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L ∧
      |profile M δ L / ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1| ≤ η := by
  obtain ⟨M₀, h⟩ := uniform_relative C δ hδ hδ1 η hη
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hphase := PaperP1.OneTwoChannelPhase.positiveMain_pos L
  have hp := mul_pos hm hphase
  refine ⟨hp, ?_⟩
  have heq : profile M δ L / ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) - 1 =
      (profile M δ L - (M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) /
        ((M : ℝ) * PaperP1.OneTwoChannelPhase.positiveMain L) := by field_simp [hm.ne', hphase.ne']
  rw [heq, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_assoc] using h M hM L hcrit)

end PaperP1.MacroscopicRationalProfile
