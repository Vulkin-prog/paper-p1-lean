module

public import PaperP1.Arithmetic.SeparatedUnitCount
public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem
public import PaperP1.Model.BoundaryAlignedPairs

/-! # Separated height-one boundary pairs cannot carry a fixed positive rank density -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedHeightOneRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      x + L ≤ y → EnlargedPairGeometry.Geometric 1 1 x y L →
      (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Nr, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C ε hε
  refine ⟨max 2 Nr, by omega, ?_⟩
  intro N hN L hcrit x hx y hy hsep hgeom
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have hh := (mem_Ico.mp hy).1; omega
  have hcard := SeparatedUnitCount.height_one hxpos hypos hsep
  have hz : (NormalizedUnitCount.units 1 1 x y L).card - 1 = 0 := by omega
  have hrank := (hr N (by omega) L 1 1 x y hcrit (by decide) (by decide) (by decide)
    (by simpa only [max_self] using (one_le_pow₀ (show 1 ≤ L + 1 by omega) : 1 ≤ (L + 1) ^ 3)) hx hy hgeom).1
  rw [hz, Nat.cast_zero, zero_add] at hrank
  have hinter : (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤
      NormalizedPairRankLoss.pairLoss x y L := by
    exact_mod_cast NormalizedPairRankLoss.intersection_rank_le_loss hxpos hypos
  exact hinter.trans hrank

theorem uniform_exclusion (θ C : ℝ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      x < y → x + L ≤ y →
      θ * L < (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) →
      ({x, y} : Finset ℕ) ∉ BoundaryAlignedPairs.channel N L 1 1 := by
  obtain ⟨Nr, _hNr, hr⟩ := uniform_bound C (θ / 4) (by positivity)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max Nr Ng), by omega, ?_⟩
  intro N hN L hcrit x hx y hy hxy hsep hstrong he
  obtain ⟨u, v, _hu, _hv, hpair, huv, hgeom⟩ := BoundaryAlignedPairs.data he
  have hxmem : x = u ∨ x = v := by
    have hh : x ∈ ({u, v} : Finset ℕ) := by rw [← hpair]; exact mem_insert_self _ _
    simpa only [mem_insert, mem_singleton] using hh
  have hymem : y = u ∨ y = v := by
    have hh : y ∈ ({u, v} : Finset ℕ) := by rw [← hpair]; exact mem_insert_of_mem (mem_singleton_self _)
    simpa only [mem_insert, mem_singleton] using hh
  have hp : u = x ∧ v = y := by
    rcases hxmem with hxmem | hxmem <;> rcases hymem with hymem | hymem <;> omega
  rw [hp.1, hp.2] at hgeom
  have hsmall := hr N (by omega) L hcrit x hx y hy hsep hgeom
  have hL : 0 < L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
  have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hbudget := mul_le_mul_of_nonneg_left hB (show 0 ≤ θ / 4 by positivity)
  have hpos : 0 < θ * L := mul_pos hθ (by exact_mod_cast hL)
  nlinarith only [hsmall, hstrong, hbudget, hpos]

end PaperP1.SeparatedHeightOneRank
