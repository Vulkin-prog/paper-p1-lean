module

public import PaperP1.Arithmetic.PrivateNormalizedPairLoss
public import PaperP1.Asymptotics.MacroscopicKernelExceptionHosts
public import PaperP1.Asymptotics.MacroscopicHighRelationMass

/-! # Actual fixed-channel full/rational power comparison

The error vanishes on every private normalized pair. Its literal support
has the proved square-root host count. Both powers are bounded internally;
no mass estimate or target comparison is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicFixedChannelComparison

open Finset PaperP1.Arithmetic PaperP1.NormalizedPairRankLoss
  PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicKernelExceptionHosts
  PaperP1.MacroscopicHighRelationMass

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channelPairs (M : ℕ) (δ : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric a b xy.1 xy.2 L

theorem power_error_zero {H : ℝ} {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hp : PaperP1.GoodEdgeCompression.PrivateAbove H (PaperP1.NormalizedWindowSets.union a b x y L)) :
    |(2 ^ pairLoss x y L : ℝ) - 2 ^ ((units a b x y L).card - 1)| = 0 := by
  rw [PaperP1.PrivateNormalizedPairLoss.loss_eq_units_privateAbove ha hb hx hy hp, sub_self, abs_zero]

theorem affine_error_le (η : Bool) (r s : ℕ) :
    |affineWeight η r - affineWeight η s| ≤ |(2 ^ r : ℝ) - 2 ^ s| := by
  cases η with
  | false => simp [affineWeight]
  | true =>
    have h : affineWeight true r - affineWeight true s = (2 ^ r : ℝ) - 2 ^ s := by simp [affineWeight]
    rw [h]

theorem uniform_power_error (C δ : ℝ) (hδ : 0 < δ) (Q q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → a.Coprime b →
      q ≤ b → b ≤ Q → ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ a b L →
      (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)|) ≤
        (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MN, hN⟩ := nonprivate_count C Q (ε / 2) (by positivity)
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicRelationPowers.uniform_channel C δ hδ q hq (ε / 2) (by positivity)
  obtain ⟨MU, hU⟩ := PaperP1.MacroscopicRelationPowers.uniform_rational_units C q hq (ε / 2) (by positivity)
  obtain ⟨MG, hG⟩ := uniform_geometry C δ Q hδ
  refine ⟨max MN (max MR (max MU MG)), ?_⟩
  intro M hM L a b hcrit ha hab hcop hqb hbQ E hE
  have hm2 : 2 ≤ M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let S := E ∩ nonprivatePairs M δ (cutoff Q L) a b L
  have hsupp : (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)|) =
      ∑ xy ∈ S, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)| := by
    symm
    apply sum_subset inter_subset_left
    intro xy hxy hnS
    obtain ⟨hblock, hg⟩ := mem_filter.mp (hE hxy)
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have hp : PaperP1.GoodEdgeCompression.PrivateAbove (cutoff Q L : ℝ)
        (PaperP1.NormalizedWindowSets.union a b xy.1 xy.2 L) := by
      by_contra hbad
      exact hnS (mem_inter.mpr ⟨hxy, mem_filter.mpr ⟨hblock, hg, hbad⟩⟩)
    exact power_error_zero ha (ha.trans_le hab) (starts_pos hm2 hδ hx) (starts_pos hm2 hδ hy) hp
  have hpoint : ∀ xy ∈ S, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)| ≤
      (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp (hE (mem_inter.mp hxy).1)
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have hwidth := (hG M (by omega) L hcrit xy.1 hx).1
    have hpowwidth : Q ≤ (L + 1) ^ 3 := hwidth.trans (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
    have hp := hR M (by omega) L a b xy.1 xy.2 hcrit ha hab hcop hqb (hbQ.trans hpowwidth) hx hy hg
    have hu := hU M (by omega) L a b xy.1 xy.2 hcrit ha (ha.trans_le hab) hcop hqb
      (by have := starts_pos hm2 hδ hx; omega) (by have := starts_pos hm2 hδ hy; omega)
    apply abs_le.mpr
    constructor <;> nlinarith only [hp, hu, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pairLoss xy.1 xy.2 L),
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((units a b xy.1 xy.2 L).card - 1)]
  have hc : (S.card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε / 2) := by
    have hsub : S ⊆ nonprivatePairs M δ (cutoff Q L) a b L := inter_subset_right
    have hcard : (S.card : ℝ) ≤ (nonprivatePairs M δ (cutoff Q L) a b L).card := by exact_mod_cast card_le_card hsub
    exact hcard.trans (hN M (by omega) δ hδ L a b hcrit ha hab hbQ)
  rw [hsupp]
  calc
    _ ≤ ∑ _xy ∈ S, (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := sum_le_sum hpoint
    _ = S.card * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) ^ (1 / 2 + ε / 2) * (M : ℝ) ^ (1 / (q : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by rw [← Real.rpow_add hm]; congr 1; ring

theorem uniform_weight_errors (C δ : ℝ) (hδ : 0 < δ) (Q q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → a.Coprime b →
      q ≤ b → b ≤ Q → ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ a b L →
      |(∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) -
        ∑ xy ∈ E, ((2 ^ ((units a b xy.1 xy.2 L).card - 1) : ℝ) - 1)| ≤
          (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) ∧
      ∀ η : ℕ × ℕ → Bool,
        (∑ xy ∈ E, |affineWeight (η xy) (pairLoss xy.1 xy.2 L) -
          affineWeight (η xy) ((units a b xy.1 xy.2 L).card - 1)|) ≤
          (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := uniform_power_error C δ hδ Q q hq ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b hcrit ha hab hcop hqb hbQ E hE
  have hs := h M hM L a b hcrit ha hab hcop hqb hbQ E hE
  constructor
  · rw [← sum_sub_distrib]
    have heq : (∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 - (2 ^ ((units a b xy.1 xy.2 L).card - 1) - 1))) =
        ∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)) := by
      apply sum_congr rfl
      intro xy _
      ring
    rw [heq]
    exact (abs_sum_le_sum_abs _ _).trans hs
  · intro η
    exact (sum_le_sum fun xy _ ↦ affine_error_le (η xy) (pairLoss xy.1 xy.2 L) ((units a b xy.1 xy.2 L).card - 1)).trans hs

theorem height_two (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ 1 2 L →
      |(∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) -
        ∑ xy ∈ E, ((2 ^ ((units 1 2 xy.1 xy.2 L).card - 1) : ℝ) - 1)| ≤ (M : ℝ) ^ (1 + ε) ∧
      ∀ η : ℕ × ℕ → Bool,
        (∑ xy ∈ E, |affineWeight (η xy) (pairLoss xy.1 xy.2 L) -
          affineWeight (η xy) ((units 1 2 xy.1 xy.2 L).card - 1)|) ≤ (M : ℝ) ^ (1 + ε) := by
  obtain ⟨M₀, h⟩ := uniform_weight_errors C δ hδ 2 2 (by norm_num) ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit E hE
  simpa only [Nat.cast_ofNat, show (1 : ℝ) / 2 + 1 / (2 : ℝ) + ε = 1 + ε by ring] using
    h M hM L 1 2 hcrit (by norm_num) (by omega) (by norm_num) (by omega) (by omega) E hE


theorem channel_swap (M a b L : ℕ) (δ : ℝ) :
    (channelPairs M δ a b L).image Prod.swap = channelPairs M δ b a L := by
  ext xy
  constructor
  · intro hxy
    obtain ⟨uv, huv, rfl⟩ := mem_image.mp hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp huv
    obtain ⟨hu, hv⟩ := mem_product.mp hblock
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hv, hu⟩, (geometric_swap a b uv.1 uv.2 L).mp hg⟩
  · intro hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    refine mem_image.mpr ⟨xy.swap, ?_, by simp⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, (geometric_swap b a xy.1 xy.2 L).mp hg⟩

theorem uniform_power_error_height (C δ : ℝ) (hδ : 0 < δ) (Q q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → 0 < b → a.Coprime b →
      q ≤ max a b → a ≤ Q → b ≤ Q → ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ a b L →
      (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)|) ≤
        (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := uniform_power_error C δ hδ Q q hq ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b hcrit ha hb hcop hqmax haQ hbQ E hE
  by_cases hab : a ≤ b
  · exact h M hM L a b hcrit ha hab hcop (by simpa only [max_eq_right hab] using hqmax) hbQ E hE
  · have hba : b ≤ a := by omega
    have hsub : E.image Prod.swap ⊆ channelPairs M δ b a L := by
      rw [← channel_swap M a b L δ]
      exact Finset.image_mono Prod.swap hE
    have hs := h M hM L b a hcrit hb hba hcop.symm
      (by simpa only [max_eq_left hba] using hqmax) haQ (E.image Prod.swap) hsub
    have heq : (∑ xy ∈ E.image Prod.swap,
        |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units b a xy.1 xy.2 L).card - 1)|) =
        ∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)| := by
      rw [sum_image]
      · apply sum_congr rfl
        intro xy hxy
        obtain ⟨hblock, _hg⟩ := mem_filter.mp (hE hxy)
        obtain ⟨hx, hy⟩ := mem_product.mp hblock
        change |(2 ^ pairLoss xy.2 xy.1 L : ℝ) - 2 ^ ((units b a xy.2 xy.1 L).card - 1)| = _
        rw [pairLoss_comm xy.2 xy.1 L, ← units_card_swap ha hb
          (by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega)
          (by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega)]
      · intro xy _ uv _ heq
        have hh := congrArg Prod.swap heq
        simpa only [Prod.swap_swap] using hh
    rw [heq] at hs
    exact hs

end PaperP1.MacroscopicFixedChannelComparison
