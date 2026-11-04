module

public import PaperP1.Arithmetic.RationalUnitCodeSupport
public import PaperP1.Asymptotics.MacroscopicChannelPartition

/-! # Uniform canonical rational-code identification on the original macroscopic roots

The code is global and chosen before a channel witness. Its exact dimension
and off-alignment vanishing are transported with one moving-height threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicRationalCodeGeometry

open Finset PaperP1.Arithmetic PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.EnlargedPairGeometry PaperP1.MacroscopicIntervalGeometry
  PaperP1.MacroscopicHighRelationMass PaperP1.MacroscopicChannelPartition

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_geometry (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < L ∧ ∀ x ∈ starts M δ, L + 1 < x ∧ 4 * (L + 1) ^ 7 < x := by
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ 4 hδ (by norm_num) 7
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MP MG, ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  refine ⟨hL, ?_⟩
  intro x hx
  have hlarge : 4 * (L + 1) ^ 7 < x := by exact_mod_cast hP M (by omega) L hcrit x hx
  have hpow : L + 1 ≤ (L + 1) ^ 7 := le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 7 ≠ 0)
  exact ⟨by omega, hlarge⟩

theorem uniform_channel (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ x ∈ starts M δ, ∀ y ∈ starts M δ,
      ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      Geometric a b x y L →
      PaperP1.RationalUnitCode.nullity x y L = (units a b x y L).card - 1 ∧
      PaperP1.RationalUnitCode.weight x y L ≤ (2 ^ pairLoss x y L : ℝ) - 1 := by
  obtain ⟨M₀, hG⟩ := uniform_geometry C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit x hx y hy a b ha hb hab haB hbB hg
  obtain ⟨hL, hroot⟩ := hG M hM L hcrit
  obtain ⟨hxB, _hxlarge⟩ := hroot x hx
  obtain ⟨hyB, hylarge⟩ := hroot y hy
  exact ⟨PaperP1.RationalUnitCode.nullity_eq_units ha hb hab hL hxB hyB haB hbB hylarge hg,
    PaperP1.RationalUnitCodeSupport.weight_le_full ha hb hab hL hxB hyB haB hbB hylarge hg⟩

theorem uniform_off_channel (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ x ∈ starts M δ, ∀ y ∈ starts M δ,
      (x, y) ∉ highPairs M δ L 1 →
      PaperP1.RationalUnitCode.nullity x y L = 0 ∧ PaperP1.RationalUnitCode.weight x y L = 0 := by
  obtain ⟨M₀, hG⟩ := uniform_geometry C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit x hx y hy hn
  obtain ⟨hL, hroot⟩ := hG M hM L hcrit
  have hno : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      ¬Geometric a b x y L := by
    intro a b ha hb hab haB hbB hg
    apply hn
    apply mem_biUnion.mpr
    refine ⟨(a, b), mem_filter.mpr ⟨?_, by omega, hab⟩, mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hg⟩⟩
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, haB⟩, mem_Icc.mpr ⟨by omega, hbB⟩⟩
  exact ⟨PaperP1.RationalUnitCodeSupport.nullity_zero_of_no_channel hL (hroot x hx).1 (hroot y hy).1 hno,
    PaperP1.RationalUnitCodeSupport.weight_zero_of_no_channel hL (hroot x hx).1 (hroot y hy).1 hno⟩

theorem uniform_aligned_bound (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ xy ∈ aligned M δ L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 := by
  obtain ⟨M₀, h⟩ := uniform_channel C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit xy hxy
  obtain ⟨hh, _hsep⟩ := mem_filter.mp hxy
  obtain ⟨⟨a, b⟩, hab, hpair⟩ := mem_biUnion.mp hh
  obtain ⟨hcoeff, _hq, hcop⟩ := mem_filter.mp hab
  obtain ⟨haI, hbI⟩ := mem_product.mp hcoeff
  obtain ⟨ha1, haB⟩ := mem_Icc.mp haI
  obtain ⟨hb1, hbB⟩ := mem_Icc.mp hbI
  obtain ⟨hblock, hg⟩ := mem_filter.mp hpair
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact (h M hM L hcrit xy.1 hx xy.2 hy a b (by omega) (by omega) hcop haB hbB hg).2

theorem uniform_low_zero (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L = 0 := by
  obtain ⟨M₀, h⟩ := uniform_channel C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit xy hxy
  obtain ⟨hchan, _hsep⟩ := mem_filter.mp hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hchan
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have heq := (h M hM L hcrit xy.1 hx xy.2 hy 1 1 (by omega) (by omega) (by norm_num)
    (one_le_pow₀ (by omega : 1 ≤ L + 1)) (one_le_pow₀ (by omega : 1 ≤ L + 1)) hg).1
  rw [PaperP1.MacroscopicSeparatedHeightOne.units_card_zero (by omega : 2 ≤ M) hδ hxy] at heq
  rw [PaperP1.RationalUnitCode.weight, heq]
  norm_num

end PaperP1.MacroscopicRationalCodeGeometry
