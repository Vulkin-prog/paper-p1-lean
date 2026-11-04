module

public import PaperP1.Arithmetic.SeparatedNormalizedUnits
public import PaperP1.Asymptotics.MacroscopicFixedChannelComparison

/-! # The actual separated height-one profile is subpolynomial per host

The rational contribution is exactly zero. Actual full residual powers
are summed over their proved linear-times-width geometric host set.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicSeparatedHeightOne

open Finset PaperP1.Arithmetic PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicFixedChannelComparison
  PaperP1.MacroscopicHighRelationMass PaperP1.CriticalBandScale

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (M : ℕ) (δ : ℝ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (channelPairs M δ 1 1 L).filter fun xy ↦ L < Nat.dist xy.1 xy.2

theorem subset_bounded {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    pairs M δ L ⊆ PaperP1.BoundedGeometricPairCount.pairs M L 1 1 := by
  intro xy hxy
  obtain ⟨hchan, _hsep⟩ := mem_filter.mp hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hchan
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Ico.mpr ⟨starts_pos hM hδ hx, (mem_starts_iff.mp hx).2⟩,
      mem_Ico.mpr ⟨starts_pos hM hδ hy, (mem_starts_iff.mp hy).2⟩⟩, hg⟩

theorem card_bound {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (pairs M δ L).card ≤ 5 * M * (L + 1) := by
  have hc := (card_le_card (subset_bounded hM hδ (L := L))).trans
    (PaperP1.BoundedGeometricPairCount.pairs_card (M := M) (L := L) (a := 1) (b := 1) (by omega))
  have hfac : 2 * (1 + 1) * (L + 1) + 1 ≤ 5 * (L + 1) := by omega
  have hh := Nat.mul_le_mul_left M hfac
  nlinarith only [hc, hh]

theorem units_card_zero {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ)
    {xy : ℕ × ℕ} (hxy : xy ∈ pairs M δ L) : (units 1 1 xy.1 xy.2 L).card = 0 := by
  obtain ⟨hchan, hsep⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hchan).1
  rw [PaperP1.SeparatedNormalizedUnits.units_empty
    (by have := starts_pos hM hδ hx; omega) (by have := starts_pos hM hδ hy; omega) hsep, card_empty]

theorem uniform_power_sum (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ pairs M δ L, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤ (M : ℝ) ^ (1 + ε) := by
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicRelationPowers.uniform_no_units C δ hδ (ε / 2) (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 5 1 (ε / 2) (by positivity)
  obtain ⟨MB, hB⟩ := critical_band_scale C
  refine ⟨max MR (max MP MB), ?_⟩
  intro M hM L hcrit
  have hm2 : 2 ≤ M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hpoint : ∀ xy ∈ pairs M δ L,
      (2 ^ pairLoss xy.1 xy.2 L : ℝ) ≤ (M : ℝ) ^ (ε / 2) := by
    intro xy hxy
    obtain ⟨hchan, _hsep⟩ := mem_filter.mp hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hchan
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact hR M (by omega) L 1 1 xy.1 xy.2 hcrit (by omega) (by omega)
      (one_le_pow₀ (by omega : 1 ≤ L + 1)) hx hy hg (units_card_zero hm2 hδ hxy)
  have hcard : ((pairs M δ L).card : ℝ) ≤ 5 * M * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast card_bound hm2 hδ (L := L)
  have hpoly : 5 * ((L + 1 : ℕ) : ℝ) ≤ (M : ℝ) ^ (ε / 2) := by
    have hp := hP M (by omega) L (hB M (by omega) L hcrit).2
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * (L + 1 : ℝ) ^ 1)] at hp
    simpa only [pow_one, Nat.cast_add, Nat.cast_one] using hp
  calc
    _ ≤ ∑ _xy ∈ pairs M δ L, (M : ℝ) ^ (ε / 2) := sum_le_sum hpoint
    _ = (pairs M δ L).card * (M : ℝ) ^ (ε / 2) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (5 * M * ((L + 1 : ℕ) : ℝ)) * (M : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) * (5 * ((L + 1 : ℕ) : ℝ)) * (M : ℝ) ^ (ε / 2) := by ring
    _ ≤ (M : ℝ) * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hm.le) (Real.rpow_nonneg hm.le _)
    _ = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (ε / 2) * (M : ℝ) ^ (ε / 2) := by rw [Real.rpow_one]
    _ = (M : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_add hm, ← Real.rpow_add hm]
      congr 1
      ring

theorem uniform_weights (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ pairs M δ L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)) ≤ (M : ℝ) ^ (1 + ε) ∧
      ∀ η : ℕ × ℕ → Bool,
        (∑ xy ∈ pairs M δ L, |affineWeight (η xy) (pairLoss xy.1 xy.2 L)|) ≤ (M : ℝ) ^ (1 + ε) := by
  obtain ⟨M₀, h⟩ := uniform_power_sum C δ hδ ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  have hs := h M hM L hcrit
  constructor
  · exact (sum_le_sum fun _ _ ↦ sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans hs
  · intro η
    exact (sum_le_sum fun xy _ ↦ affine_weight_abs_le (η xy) (pairLoss xy.1 xy.2 L)).trans hs

end PaperP1.MacroscopicSeparatedHeightOne
