module

public import PaperP1.Asymptotics.DyadicLeadingPairGeometry
public import PaperP1.Combinatorics.GraphStarWeights

/-! # A literal nonnegative cover of the complete dyadic aligned domain

The leading mask is a subset of the original aligned domain. All remaining
positive mass is bounded by height one, endpoints and heights at least four.
No cancellation or multiplicity assumption is needed for this cover bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPositiveCover

open Finset PaperP1.Arithmetic PaperP1.DyadicAlignedPairMasks

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem channel_subset_high_one {N L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3) : channel N L a b ⊆ high N L 1 := by
  intro xy hxy
  apply mem_biUnion.mpr
  refine ⟨(a, b), mem_filter.mpr ⟨?_, by omega, hab⟩, hxy⟩
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, haB⟩, mem_Icc.mpr ⟨by omega, hbB⟩⟩

theorem leading_subset {N L : ℕ} (hL : 0 < L) : leading N L ⊆ aligned N L := by
  intro xy hxy
  obtain ⟨hc, hsep⟩ := mem_filter.mp hxy
  have hpow := Nat.pow_le_pow_left (by omega : 2 ≤ L + 1) 3
  norm_num at hpow
  rcases mem_union.mp hc with hc | hc
  · exact mem_filter.mpr ⟨channel_subset_high_one (by omega : 0 < 2) (by omega : 0 < 3)
      (by norm_num : Nat.Coprime 2 3) (by omega) (by omega) hc, hsep⟩
  · exact mem_filter.mpr ⟨channel_subset_high_one (by omega : 0 < 3) (by omega : 0 < 2)
      (by norm_num : Nat.Coprime 3 2) (by omega) (by omega) hc, hsep⟩

theorem cover {N L : ℕ} (h13 : channel N L 1 3 = ∅) (h31 : channel N L 3 1 = ∅) :
    aligned N L ⊆ ((separated (channel N L 1 1) L ∪ boundary N L) ∪ leading N L) ∪ separated (high N L 4) L := by
  intro xy hxy
  obtain ⟨hh, hsep⟩ := mem_filter.mp hxy
  obtain ⟨⟨a, b⟩, hab, hpair⟩ := mem_biUnion.mp hh
  obtain ⟨hcoeff, _hq, hcop⟩ := mem_filter.mp hab
  obtain ⟨haI, hbI⟩ := mem_product.mp hcoeff
  obtain ⟨ha, _haB⟩ := mem_Icc.mp haI
  obtain ⟨hb, _hbB⟩ := mem_Icc.mp hbI
  by_cases hhigh : 4 ≤ max a b
  · exact mem_union_right _ (mem_filter.mpr
      ⟨mem_biUnion.mpr ⟨(a, b), mem_filter.mpr ⟨hcoeff, hhigh, hcop⟩, hpair⟩, hsep⟩)
  · have ha3 : a ≤ 3 := by omega
    have hb3 : b ≤ 3 := by omega
    by_cases ha1 : a = 1
    · subst a
      interval_cases b
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hpair, hsep⟩)))
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_left _ hpair, hsep⟩)))
      · rw [h13] at hpair
        exact False.elim (notMem_empty _ hpair)
    · by_cases ha2 : a = 2
      · subst a
        interval_cases b
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_right _ hpair, hsep⟩)))
        · norm_num at hcop
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_left _ hpair, hsep⟩))
      · have ha' : a = 3 := by omega
        subst a
        interval_cases b
        · rw [h31] at hpair
          exact False.elim (notMem_empty _ hpair)
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_union_right _ hpair, hsep⟩))
        · norm_num at hcop

theorem finite_bound {N L : ℕ} (hL : 0 < L) (h13 : channel N L 1 3 = ∅) (h31 : channel N L 3 1 = ∅)
    (f : ℕ × ℕ → ℝ) (hf : ∀ xy, 0 ≤ f xy) :
    (∑ xy ∈ leading N L, f xy) ≤ (∑ xy ∈ aligned N L, f xy) ∧
      (∑ xy ∈ aligned N L, f xy) - (∑ xy ∈ leading N L, f xy) ≤
        (∑ xy ∈ separated (channel N L 1 1) L, f xy) + (∑ xy ∈ boundary N L, f xy) +
          (∑ xy ∈ separated (high N L 4) L, f xy) := by
  have hsub := cover h13 h31
  have hupper := sum_le_sum_of_subset_of_nonneg hsub (fun xy _ _ ↦ hf xy)
  have h1 := PaperP1.GraphStarWeights.sum_union_le_nonneg (separated (channel N L 1 1) L) (boundary N L) f hf
  have h2 := PaperP1.GraphStarWeights.sum_union_le_nonneg (separated (channel N L 1 1) L ∪ boundary N L) (leading N L) f hf
  have h3 := PaperP1.GraphStarWeights.sum_union_le_nonneg ((separated (channel N L 1 1) L ∪ boundary N L) ∪ leading N L)
    (separated (high N L 4) L) f hf
  refine ⟨sum_le_sum_of_subset_of_nonneg (leading_subset hL) (fun xy _ _ ↦ hf xy), ?_⟩
  linarith only [hupper, h1, h2, h3]

theorem uniform_bound (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ f : ℕ × ℕ → ℝ, (∀ xy, 0 ≤ f xy) →
      (∑ xy ∈ leading N L, f xy) ≤ (∑ xy ∈ aligned N L, f xy) ∧
      (∑ xy ∈ aligned N L, f xy) - (∑ xy ∈ leading N L, f xy) ≤
        (∑ xy ∈ separated (channel N L 1 1) L, f xy) + (∑ xy ∈ boundary N L, f xy) +
          (∑ xy ∈ separated (high N L 4) L, f xy) := by
  obtain ⟨MA, hA⟩ := PaperP1.DyadicLeadingPairGeometry.uniform_one_three_absent C
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MA MG, ?_⟩
  intro N hN L hcrit f hf
  obtain ⟨h13, h31⟩ := hA N (by omega) L hcrit
  have hL : 0 < L := by have := (hG N (by omega) L hcrit).2.2.1; omega
  exact finite_bound hL h13 h31 f hf

end PaperP1.DyadicPositiveCover
