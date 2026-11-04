module

public import PaperP1.Model.ActualAffinePairWeight
public import PaperP1.Asymptotics.MacroscopicSeparatedHeightOne
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Literal signed affine mass in the actual exceptional macroscopic sectors

The actual event determines compatibility; each mass is a sum of absolute
actual signed weights. No arbitrary surrogate phase is used here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicActualSignedMass

open Finset PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicHighRelationMass
  PaperP1.NormalizedPairRankLoss

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem weight_eq_affine {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) :
    PaperP1.ActualAffinePairWeight.weight x y L =
      affineWeight (PaperP1.ActualAffinePairWeight.compatibility x y L) (pairLoss x y L) :=
  PaperP1.ActualAffinePairWeight.weight_eq_compatibility hx hy hL

theorem uniform_high (C δ : ℝ) (hδ : 0 < δ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ highPairs M δ L q, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L|) ≤
        (M : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MH, hH⟩ := uniform_power_sum C δ hδ q hq ε hε
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MH MG, ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hpoint : ∀ xy ∈ highPairs M δ L q,
      |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L| ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ) := by
    intro xy hxy
    obtain ⟨ab, _hab, hpair⟩ := mem_biUnion.mp hxy
    obtain ⟨hblock, _hg⟩ := mem_filter.mp hpair
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact PaperP1.ActualAffinePairWeight.abs_weight_le
      (by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega)
      (by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega) hL
  exact (sum_le_sum hpoint).trans (hH M (by omega) L hcrit)

theorem high_height_three (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ highPairs M δ L 3, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L|) ≤
        (M : ℝ) ^ (4 / 3 + ε) := by
  have hh := uniform_high C δ hδ 3 (by omega) ε hε
  simpa only [Nat.cast_ofNat, show (1 : ℝ) + 1 / (3 : ℝ) + ε = 4 / 3 + ε by ring] using hh

theorem uniform_height_one (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      (∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L,
        |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L|) ≤ (M : ℝ) ^ (1 + ε) := by
  obtain ⟨MH, hH⟩ := PaperP1.MacroscopicSeparatedHeightOne.uniform_power_sum C δ hδ ε hε
  obtain ⟨MG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max MH MG, ?_⟩
  intro M hM L hcrit
  have hL : 0 < L := by have := (hG M (by omega) L hcrit).2.2.1; omega
  have hpoint : ∀ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs M δ L,
      |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L| ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ) := by
    intro xy hxy
    obtain ⟨hchan, _hsep⟩ := mem_filter.mp hxy
    obtain ⟨hblock, _hg⟩ := mem_filter.mp hchan
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact PaperP1.ActualAffinePairWeight.abs_weight_le
      (by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega)
      (by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega) hL
  exact (sum_le_sum hpoint).trans (hH M (by omega) L hcrit)

end PaperP1.MacroscopicActualSignedMass
