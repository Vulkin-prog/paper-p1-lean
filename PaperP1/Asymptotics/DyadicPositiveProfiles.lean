module

public import PaperP1.Asymptotics.DyadicPositiveRemainder
public import PaperP1.Asymptotics.DyadicLeadingPositiveProfile

/-! # Complete actual and global rational positive dyadic profiles

R_rat is defined on every original ordered separated pair, before proving
its aligned support. Both complete profiles have the same finite leading
main term; all error-sector and leading estimates are internal.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPositiveProfiles

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.DyadicAlignedPairMasks PaperP1.DyadicPositiveRemainder PaperP1.UnsignedUnitFourierAggregate

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def positive (N L : ℕ) : ℝ := ∑ xy ∈ aligned N L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)

def rational (N L : ℕ) : ℝ :=
  ∑ xy ∈ separated ((dyadicBlock N) ×ˢ (dyadicBlock N)) L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L

theorem uniform_pointwise (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N),
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 := by
  obtain ⟨MC, hC⟩ := PaperP1.DyadicRationalCodeGeometry.uniform_channel C
  obtain ⟨MO, hO⟩ := PaperP1.DyadicRationalCodeGeometry.uniform_off_channel C
  refine ⟨max MC MO, ?_⟩
  intro N hN L hcrit xy hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  by_cases hh : xy ∈ high N L 1
  · obtain ⟨⟨a, b⟩, hab, hpair⟩ := mem_biUnion.mp hh
    obtain ⟨hcoeff, _hq, hcop⟩ := mem_filter.mp hab
    obtain ⟨haI, hbI⟩ := mem_product.mp hcoeff
    obtain ⟨ha1, haB⟩ := mem_Icc.mp haI
    obtain ⟨hb1, hbB⟩ := mem_Icc.mp hbI
    exact (hC N (by omega) L hcrit xy.1 hx xy.2 hy a b (by omega) (by omega) hcop haB hbB (mem_filter.mp hpair).2).2
  · rw [(hO N (by omega) L hcrit xy.1 hx xy.2 hy hh).2]
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem uniform_support_eq (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      rational N L = ∑ xy ∈ aligned N L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L := by
  obtain ⟨N₀, hO⟩ := PaperP1.DyadicRationalCodeGeometry.uniform_off_channel C
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit
  symm
  have hsub : aligned N L ⊆ separated ((dyadicBlock N) ×ˢ (dyadicBlock N)) L := by
    intro xy hxy
    obtain ⟨hh, hsep⟩ := mem_filter.mp hxy
    exact mem_filter.mpr ⟨high_square N L 1 hh, hsep⟩
  apply sum_subset hsub
  intro xy hxy hn
  obtain ⟨hblock, hsep⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact (hO N hN L hcrit xy.1 hx xy.2 hy (fun hh ↦ hn (mem_filter.mpr ⟨hh, hsep⟩))).2

theorem uniform_leading_rational (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ leading N L, PaperP1.RationalUnitCode.weight xy.1 xy.2 L) =
        PaperP1.DyadicLeadingPositiveProfile.rationalTotal N L := by
  obtain ⟨MC, hC⟩ := PaperP1.DyadicRationalCodeGeometry.uniform_channel C
  obtain ⟨MS, hS⟩ := PaperP1.DyadicLeadingPairGeometry.uniform_symmetric_sum C
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 3
  refine ⟨max MC (max MS MG), ?_⟩
  intro N hN L hcrit
  have hsmall : 3 ≤ L + 1 := (hG N (by omega) L hcrit).2.1
  have hB : 3 ≤ (L + 1) ^ 3 := hsmall.trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hforward : ∀ xy ∈ channel N L 2 3,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L = unitWeight 2 3 xy.1 xy.2 L := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have heq := (hC N (by omega) L hcrit xy.1 hx xy.2 hy 2 3 (by omega) (by omega) (by norm_num) (by omega) hB hg).1
    rw [PaperP1.RationalUnitCode.weight, heq]
    rfl
  have hreverse : ∀ xy ∈ channel N L 3 2,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L = unitWeight 2 3 xy.2 xy.1 L := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have heq := (hC N (by omega) L hcrit xy.1 hx xy.2 hy 3 2 (by omega) (by omega) (by norm_num) hB (by omega) hg).1
    have hcard := units_card_swap (x := xy.1) (y := xy.2) (L := L) (by omega : 0 < 3) (by omega : 0 < 2)
      (by have := (mem_Ico.mp hx).1; omega) (by have := (mem_Ico.mp hy).1; omega)
    rw [PaperP1.RationalUnitCode.weight, heq, hcard]
    rfl
  obtain ⟨heq, hdis, _hsum⟩ := hS N (by omega) L hcrit
  rw [heq, sum_union hdis, sum_congr rfl hforward, sum_congr rfl hreverse]
  have hswap : (∑ xy ∈ channel N L 3 2, unitWeight 2 3 xy.2 xy.1 L) =
      ∑ xy ∈ channel N L 2 3, unitWeight 2 3 xy.1 xy.2 L := by
    rw [← channel_swap N L 2 3, sum_image]
    · rfl
    · intro xy _ uv _ hh
      have hk := congrArg Prod.swap hh
      simpa only [Prod.swap_swap] using hk
  rw [hswap, PaperP1.DyadicLeadingPairGeometry.rational_forward_sum (by omega : 2 ≤ N)]
  unfold PaperP1.DyadicLeadingPositiveProfile.rationalTotal
  ring

theorem uniform_positive_main (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |positive N L - (N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ)| ≤ (N : ℝ) ^ (5 / 4 + ε) := by
  obtain ⟨MR, hR⟩ := uniform_remainder C (ε / 2) (by positivity)
  obtain ⟨ML, hL⟩ := PaperP1.DyadicLeadingPositiveProfile.uniform_main_term C (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (5 / 4 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MR (max ML MF), ?_⟩
  intro N hN L hcrit
  obtain ⟨hr0, hr⟩ := hR N (by omega) L hcrit (fun xy ↦ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)
    (fun _ ↦ sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (fun _ _ ↦ sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1))
  have hl := hL N (by omega) L hcrit
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (5 / 6 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hf : 2 * (N : ℝ) ^ (5 / 4 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
    simpa only [show (5 : ℝ) / 4 + ε / 2 + ε / 2 = 5 / 4 + ε by ring] using hF N (by omega)
  have ht := abs_sub_le (positive N L) (PaperP1.DyadicLeadingPositiveProfile.positive N L)
    ((N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ))
  change 0 ≤ positive N L - PaperP1.DyadicLeadingPositiveProfile.positive N L at hr0
  change positive N L - PaperP1.DyadicLeadingPositiveProfile.positive N L ≤ _ at hr
  rw [abs_of_nonneg hr0] at ht
  exact ht.trans ((by linarith only [hr, hl.trans hpower] : _ ≤ 2 * (N : ℝ) ^ (5 / 4 + ε / 2)).trans hf)

theorem uniform_rational_main (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |rational N L - (N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ)| ≤ (N : ℝ) ^ (5 / 4 + ε) := by
  obtain ⟨MP, hP⟩ := uniform_pointwise C
  obtain ⟨MS, hS⟩ := uniform_support_eq C
  obtain ⟨MR, hR⟩ := uniform_remainder C (ε / 2) (by positivity)
  obtain ⟨ML, hL⟩ := uniform_leading_rational C
  obtain ⟨ME, hE⟩ := PaperP1.DyadicLeadingPositiveProfile.endpoint_rate C (ε / 2) (by positivity)
  obtain ⟨MG, hG⟩ := PaperP1.CriticalPolynomialScale.polynomial_lt_scale C 5 (by norm_num) 1
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (5 / 4 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MP (max MS (max MR (max ML (max ME (max MG MF))))), ?_⟩
  intro N hN L hcrit
  have hpoint : ∀ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), PaperP1.RationalUnitCode.weight xy.1 xy.2 L ≤
      (2 ^ pairLoss xy.1 xy.2 L : ℝ) :=
    fun xy hxy ↦ (hP N (by omega) L hcrit xy hxy).trans (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨hr0, hr⟩ := hR N (by omega) L hcrit (fun xy ↦ PaperP1.RationalUnitCode.weight xy.1 xy.2 L)
    (fun xy ↦ PaperP1.RationalUnitCode.weight_nonneg xy.1 xy.2 L) hpoint
  rw [← hS N (by omega) L hcrit, hL N (by omega) L hcrit] at hr0 hr
  have hg := hG N (by omega) L hcrit
  simp only [pow_one] at hg
  have hlarge : 5 * (L + 1) < N := by exact_mod_cast hg
  have he := (PaperP1.DyadicLeadingPositiveProfile.finite_error (by omega : 2 ≤ N) hlarge).trans
    (hE N (by omega) L hcrit)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (1 / 3 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hf : 2 * (N : ℝ) ^ (5 / 4 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
    simpa only [show (5 : ℝ) / 4 + ε / 2 + ε / 2 = 5 / 4 + ε by ring] using hF N (by omega)
  have ht := abs_sub_le (rational N L) (PaperP1.DyadicLeadingPositiveProfile.rationalTotal N L)
    ((N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ))
  rw [abs_of_nonneg hr0] at ht
  exact ht.trans ((by linarith only [hr, he.trans hpower] : _ ≤ 2 * (N : ℝ) ^ (5 / 4 + ε / 2)).trans hf)

theorem uniform_domination (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 ≤ rational N L ∧ rational N L ≤ positive N L := by
  obtain ⟨MS, hS⟩ := uniform_support_eq C
  obtain ⟨MP, hP⟩ := uniform_pointwise C
  refine ⟨max MS MP, ?_⟩
  intro N hN L hcrit
  constructor
  · exact sum_nonneg fun xy _ ↦ PaperP1.RationalUnitCode.weight_nonneg xy.1 xy.2 L
  · rw [hS N (by omega) L hcrit]
    exact sum_le_sum fun xy hxy ↦ hP N (by omega) L hcrit xy (high_square N L 1 (mem_filter.mp hxy).1)

theorem uniform_comparison (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 ≤ positive N L - rational N L ∧ positive N L - rational N L ≤ (N : ℝ) ^ (5 / 4 + ε) := by
  obtain ⟨MD, hD⟩ := uniform_domination C
  obtain ⟨MP, hP⟩ := uniform_positive_main C (ε / 2) (by positivity)
  obtain ⟨MR, hR⟩ := uniform_rational_main C (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (5 / 4 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MD (max MP (max MR MF)), ?_⟩
  intro N hN L hcrit
  have hd : 0 ≤ positive N L - rational N L := sub_nonneg.mpr (hD N (by omega) L hcrit).2
  have hp := hP N (by omega) L hcrit
  have hr := hR N (by omega) L hcrit
  have hf : 2 * (N : ℝ) ^ (5 / 4 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
    simpa only [show (5 : ℝ) / 4 + ε / 2 + ε / 2 = 5 / 4 + ε by ring] using hF N (by omega)
  have ht := abs_sub_le (positive N L) ((N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ)) (rational N L)
  rw [abs_of_nonneg hd, abs_sub_comm _ (rational N L)] at ht
  exact ⟨hd, ht.trans ((by linarith only [hp, hr] : _ ≤ 2 * (N : ℝ) ^ (5 / 4 + ε / 2)).trans hf)⟩

end PaperP1.DyadicPositiveProfiles
