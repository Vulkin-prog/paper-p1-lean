module

public import PaperP1.Arithmetic.BoundedHeightChannelUniqueness
public import PaperP1.Asymptotics.MacroscopicSeparatedHeightOne
public import PaperP1.Asymptotics.MacroscopicPolynomialScale

/-! # A disjoint actual aligned partition on the macroscopic interval

All enlarged reduced slopes up to B^3 are retained. The determinant
threshold proves uniqueness even when the pair has no exact unit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicChannelPartition

open Finset PaperP1.Arithmetic PaperP1.EnlargedPairGeometry
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicHighRelationMass
  PaperP1.MacroscopicFixedChannelComparison

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def aligned (M : ℕ) (δ : ℝ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (highPairs M δ L 1).filter fun xy ↦ L < Nat.dist xy.1 xy.2

def leading (M : ℕ) (δ : ℝ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (channelPairs M δ 1 2 L ∪ channelPairs M δ 2 1 L).filter fun xy ↦ L < Nat.dist xy.1 xy.2

def high (M : ℕ) (δ : ℝ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (highPairs M δ L 3).filter fun xy ↦ L < Nat.dist xy.1 xy.2

theorem channel_subset_high_one {M L a b : ℕ} {δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b) (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3) :
    channelPairs M δ a b L ⊆ highPairs M δ L 1 := by
  intro xy hxy
  apply mem_biUnion.mpr
  refine ⟨(a, b), mem_filter.mpr ⟨?_, by omega, hcop⟩, hxy⟩
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, haB⟩, mem_Icc.mpr ⟨by omega, hbB⟩⟩

theorem high_subset (M L : ℕ) (δ : ℝ) : high M δ L ⊆ aligned M δ L := by
  intro xy hxy
  obtain ⟨hh, hsep⟩ := mem_filter.mp hxy
  obtain ⟨ab, hab, hpair⟩ := mem_biUnion.mp hh
  obtain ⟨hcoeff, hq, hcop⟩ := mem_filter.mp hab
  exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨ab, mem_filter.mpr ⟨hcoeff, by omega, hcop⟩, hpair⟩, hsep⟩

theorem low_subset (M L : ℕ) (δ : ℝ) :
    PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L ⊆ aligned M δ L := by
  intro xy hxy
  obtain ⟨hchan, hsep⟩ := mem_filter.mp hxy
  exact mem_filter.mpr ⟨channel_subset_high_one (by omega : 0 < 1) (by omega : 0 < 1)
    (by norm_num : Nat.Coprime 1 1) (one_le_pow₀ (by omega : 1 ≤ L + 1)) (one_le_pow₀ (by omega : 1 ≤ L + 1)) hchan, hsep⟩

theorem leading_subset {M L : ℕ} {δ : ℝ} (hL : 0 < L) : leading M δ L ⊆ aligned M δ L := by
  intro xy hxy
  obtain ⟨hchan, hsep⟩ := mem_filter.mp hxy
  have hB : 2 ≤ (L + 1) ^ 3 := (by omega : 2 ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  rcases mem_union.mp hchan with hc | hc
  · exact mem_filter.mpr ⟨channel_subset_high_one (by omega : 0 < 1) (by omega : 0 < 2)
      (by norm_num : Nat.Coprime 1 2) (by omega) hB hc, hsep⟩
  · exact mem_filter.mpr ⟨channel_subset_high_one (by omega : 0 < 2) (by omega : 0 < 1)
      (by norm_num : Nat.Coprime 2 1) hB (by omega) hc, hsep⟩

theorem cover {M L : ℕ} {δ : ℝ} (hL : 0 < L) :
    (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L ∪ leading M δ L) ∪ high M δ L = aligned M δ L := by
  apply Subset.antisymm
  · exact union_subset (union_subset (low_subset M L δ) (leading_subset hL)) (high_subset M L δ)
  · intro xy hxy
    obtain ⟨hh, hsep⟩ := mem_filter.mp hxy
    obtain ⟨⟨a, b⟩, hab, hpair⟩ := mem_biUnion.mp hh
    obtain ⟨hcoeff, _hq, hcop⟩ := mem_filter.mp hab
    obtain ⟨haI, hbI⟩ := mem_product.mp hcoeff
    obtain ⟨ha, _haB⟩ := mem_Icc.mp haI
    obtain ⟨hb, _hbB⟩ := mem_Icc.mp hbI
    by_cases hhigh : 3 ≤ max a b
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_biUnion.mpr ⟨(a, b), mem_filter.mpr ⟨hcoeff, hhigh, hcop⟩, hpair⟩, hsep⟩)
    · have ha2 : a ≤ 2 := by omega
      have hb2 : b ≤ 2 := by omega
      by_cases ha1 : a = 1
      · subst a
        by_cases hb1 : b = 1
        · subst b
          exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hpair, hsep⟩))
        · have hb' : b = 2 := by omega
          subst b
          exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_left _ hpair, hsep⟩))
      · have ha' : a = 2 := by omega
        subst a
        have hb' : b = 1 := by
          by_contra hn
          have hb'' : b = 2 := by omega
          subst b
          norm_num at hcop
        subst b
        exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_right _ hpair, hsep⟩))

theorem channel_unique {M L a b c d x y : ℕ} {δ : ℝ}
    (ha : 0 < a) (hab : a.Coprime b) (hcd : c.Coprime d)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3)
    (hcB : c ≤ (L + 1) ^ 3) (hdB : d ≤ (L + 1) ^ 3)
    (hlarge : ∀ z ∈ starts M δ, 4 * (L + 1) ^ 7 < z)
    (hy : y ∈ starts M δ) (hg₁ : Geometric a b x y L) (hg₂ : Geometric c d x y L) :
    a = c ∧ b = d := by
  apply PaperP1.BoundedHeightChannelUniqueness.unique ha hab hcd haB hbB hcB hdB ?_ hg₁ hg₂
  have heq : 4 * ((L + 1) ^ 3) ^ 2 * (L + 1) = 4 * (L + 1) ^ 7 := by ring
  rw [heq]
  exact hlarge y hy

theorem small_disjoint_high {M L a b : ℕ} {δ : ℝ} (ha : 0 < a) (hab : a.Coprime b)
    (ha2 : a ≤ 2) (hb2 : b ≤ 2) (hL : 0 < L)
    (hlarge : ∀ z ∈ starts M δ, 4 * (L + 1) ^ 7 < z) :
    Disjoint (channelPairs M δ a b L) (highPairs M δ L 3) := by
  apply disjoint_left.mpr
  intro xy hsmall hhigh
  obtain ⟨hblock, hg₁⟩ := mem_filter.mp hsmall
  obtain ⟨_hx, hy⟩ := mem_product.mp hblock
  obtain ⟨⟨c, d⟩, hcd, hpair⟩ := mem_biUnion.mp hhigh
  obtain ⟨hcoeff, hq, hcop⟩ := mem_filter.mp hcd
  obtain ⟨hcI, hdI⟩ := mem_product.mp hcoeff
  obtain ⟨_hc, hcB⟩ := mem_Icc.mp hcI
  obtain ⟨_hd, hdB⟩ := mem_Icc.mp hdI
  have hB : 2 ≤ (L + 1) ^ 3 := (by omega : 2 ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  obtain ⟨hac, hbd⟩ := channel_unique ha hab hcop (ha2.trans hB) (hb2.trans hB) hcB hdB
    hlarge hy hg₁ (mem_filter.mp hpair).2
  omega

theorem disjoint_sectors {M L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hlarge : ∀ z ∈ starts M δ, 4 * (L + 1) ^ 7 < z) :
    Disjoint (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L) (leading M δ L) ∧
      Disjoint (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L) (high M δ L) ∧
      Disjoint (leading M δ L) (high M δ L) := by
  have hB : 2 ≤ (L + 1) ^ 3 := (by omega : 2 ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hlowhigh := small_disjoint_high (by omega : 0 < 1) (by norm_num : Nat.Coprime 1 1)
    (by omega : 1 ≤ 2) (by omega : 1 ≤ 2) hL hlarge
  have hfhigh := small_disjoint_high (by omega : 0 < 1) (by norm_num : Nat.Coprime 1 2)
    (by omega : 1 ≤ 2) (by omega : 2 ≤ 2) hL hlarge
  have hrhigh := small_disjoint_high (by omega : 0 < 2) (by norm_num : Nat.Coprime 2 1)
    (by omega : 2 ≤ 2) (by omega : 1 ≤ 2) hL hlarge
  refine ⟨?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro xy hlow hlead
    have hg₁ := (mem_filter.mp (mem_filter.mp hlow).1).2
    obtain ⟨hblock, _⟩ := mem_filter.mp (mem_filter.mp hlow).1
    have hy := (mem_product.mp hblock).2
    rcases mem_union.mp (mem_filter.mp hlead).1 with hf | hr
    · have hh := channel_unique (by omega : 0 < 1) (by norm_num : Nat.Coprime 1 1)
        (by norm_num : Nat.Coprime 1 2) (by omega) (by omega) (by omega) hB hlarge hy hg₁ (mem_filter.mp hf).2
      omega
    · have hh := channel_unique (by omega : 0 < 1) (by norm_num : Nat.Coprime 1 1)
        (by norm_num : Nat.Coprime 2 1) (by omega) (by omega) hB (by omega) hlarge hy hg₁ (mem_filter.mp hr).2
      omega
  · exact hlowhigh.mono (filter_subset _ _) (filter_subset _ _)
  · exact (hfhigh.sup_left hrhigh).mono (filter_subset _ _) (filter_subset _ _)

theorem uniform_partition (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L ∪ leading M δ L) ∪ high M δ L = aligned M δ L ∧
      Disjoint (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L) (leading M δ L) ∧
      Disjoint (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L) (high M δ L) ∧
      Disjoint (leading M δ L) (high M δ L) := by
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ 4 hδ (by norm_num) 7
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MP MG, ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hlarge : ∀ z ∈ starts M δ, 4 * (L + 1) ^ 7 < z := by
    intro z hz
    have hp := hP M (by omega) L hcrit z hz
    exact_mod_cast hp
  exact ⟨cover hL, disjoint_sectors hL hlarge⟩

theorem uniform_sum (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ f : ℕ × ℕ → ℝ,
      (∑ xy ∈ aligned M δ L, f xy) =
        (∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L, f xy) +
        (∑ xy ∈ leading M δ L, f xy) + (∑ xy ∈ high M δ L, f xy) := by
  obtain ⟨M₀, h⟩ := uniform_partition C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit f
  obtain ⟨hcover, hll, hlh, hlhigh⟩ := h M hM L hcrit
  have hd : Disjoint (PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L ∪ leading M δ L) (high M δ L) :=
    Finset.disjoint_union_left.mpr ⟨hlh, hlhigh⟩
  rw [← hcover, sum_union hd, sum_union hll]

end PaperP1.MacroscopicChannelPartition
