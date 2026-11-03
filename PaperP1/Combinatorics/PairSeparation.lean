module

public import PaperP1.Combinatorics.PairSubfamilyWeights
public import PaperP1.Combinatorics.ClosePairs

/-! # Exact ordered close and separated host sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairSeparation

open Finset

def closeHosts (G : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  PairSubfamilyWeights.hosts G (ClosePairs.pairs G L)

def separatedHosts (G : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  OrderedPairTuples.pairs G \ closeHosts G L

theorem mem_closeHosts (G : Finset ℕ) (L : ℕ) (p : ℕ × ℕ) :
    p ∈ closeHosts G L ↔ p.1 ∈ G ∧ p.2 ∈ G ∧ p.1 ≠ p.2 ∧
      p.1 ≤ p.2 + L ∧ p.2 ≤ p.1 + L := by
  classical
  constructor
  · intro hp
    obtain ⟨hx, hy, hne, he⟩ := (PairSubfamilyWeights.mem_hosts G (ClosePairs.pairs G L) p).mp hp
    obtain ⟨a, b, _ha, _hb, hab, hbL, heq⟩ := ClosePairs.data G L {p.1, p.2} he
    have hp₁ : p.1 = a ∨ p.1 = b := by
      have hmem : p.1 ∈ ({a, b} : Finset ℕ) := heq ▸ mem_insert_self _ _
      simpa only [mem_insert, mem_singleton] using hmem
    have hp₂ : p.2 = a ∨ p.2 = b := by
      have hmem : p.2 ∈ ({a, b} : Finset ℕ) := heq ▸ mem_insert_of_mem (mem_singleton_self _)
      simpa only [mem_insert, mem_singleton] using hmem
    exact ⟨hx, hy, hne, by omega, by omega⟩
  · rintro ⟨hx, hy, hne, hxL, hyL⟩
    apply (PairSubfamilyWeights.mem_hosts G (ClosePairs.pairs G L) p).mpr
    refine ⟨hx, hy, hne, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, card_pair hne⟩, ?_⟩⟩
    · exact insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩
    · by_cases hxy : p.1 < p.2
      · exact ⟨p.1, mem_insert_self _ _, p.2, mem_insert_of_mem (mem_singleton_self _), hxy, hyL⟩
      · exact ⟨p.2, mem_insert_of_mem (mem_singleton_self _), p.1, mem_insert_self _ _, by omega, hxL⟩

theorem close_subset (G : Finset ℕ) (L : ℕ) : closeHosts G L ⊆ OrderedPairTuples.pairs G := by
  intro p hp
  obtain ⟨hx, hy, hne, _, _⟩ := (mem_closeHosts G L p).mp hp
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hne⟩

theorem mem_separatedHosts (G : Finset ℕ) (L : ℕ) (p : ℕ × ℕ) :
    p ∈ separatedHosts G L ↔ p.1 ∈ G ∧ p.2 ∈ G ∧
      (p.1 + L < p.2 ∨ p.2 + L < p.1) := by
  classical
  constructor
  · intro hp
    obtain ⟨hpA, hpC⟩ := mem_sdiff.mp hp
    obtain ⟨hpG, hne⟩ := mem_filter.mp hpA
    obtain ⟨hx, hy⟩ := mem_product.mp hpG
    have hn : ¬ (p.1 ≤ p.2 + L ∧ p.2 ≤ p.1 + L) :=
      fun h ↦ hpC ((mem_closeHosts G L p).mpr ⟨hx, hy, hne, h.1, h.2⟩)
    exact ⟨hx, hy, by omega⟩
  · rintro ⟨hx, hy, hsep⟩
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, by omega⟩, ?_⟩
    intro hpC
    have hp := (mem_closeHosts G L p).mp hpC
    omega

theorem sum_partition (G : Finset ℕ) (L : ℕ) (w : ℕ × ℕ → ℝ) :
    (∑ p ∈ separatedHosts G L, w p) + (∑ p ∈ closeHosts G L, w p) =
      ∑ p ∈ OrderedPairTuples.pairs G, w p := sum_sdiff (close_subset G L)

end PaperP1.PairSeparation
