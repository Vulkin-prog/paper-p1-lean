module

public import PaperP1.Arithmetic.DyadicAlignedPairMasks
public import PaperP1.Asymptotics.AlignedSourcePairPowers
public import PaperP1.Asymptotics.MacroscopicSeparatedHeightOne

/-! # Actual dyadic high, endpoint and separated height-one power sums

The masks retain both orientations and zero-unit pairs. Every count and
pointwise full relation power is supplied by an internally proved theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicActualSectorPowers

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedPairRankLoss
  PaperP1.DyadicAlignedPairMasks PaperP1.DyadicMacroscopicTransfer PaperP1.CriticalBandScale

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_high (C : ℝ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ high N L q, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicHighRelationMass.uniform_power_sum (C + 1) (1 / 2) (by norm_num) q hq (ε / 2) (by positivity)
  obtain ⟨NF, hF⟩ := double_power (1 + 1 / (q : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MM NF, ?_⟩
  intro N hN L hcrit
  have hn2 : 2 ≤ N := by omega
  have hs : (∑ xy ∈ high N L q, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤
      ∑ xy ∈ PaperP1.MacroscopicHighRelationMass.highPairs (2 * N) (1 / 2) L q,
        (2 ^ pairLoss xy.1 xy.2 L : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (high_subset_macro hn2) (fun _ _ _ ↦ by positivity)
  have hm := hM (2 * N) (by omega) L (critical_band (by omega : 0 < N) hcrit)
  have hf : ((2 * N : ℕ) : ℝ) ^ (1 + 1 / (q : ℝ) + ε / 2) ≤ (N : ℝ) ^ (1 + 1 / (q : ℝ) + ε) := by
    simpa only [show (1 : ℝ) + 1 / (q : ℝ) + ε / 2 + ε / 2 = 1 + 1 / (q : ℝ) + ε by ring] using hF N (by omega)
  exact hs.trans (hm.trans hf)

theorem high_height_four (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ high N L 4, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
  have hh := uniform_high C 4 (by omega) ε hε
  simpa only [Nat.cast_ofNat, show (1 : ℝ) + 1 / (4 : ℝ) + ε = 5 / 4 + ε by ring] using hh

theorem boundary (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ PaperP1.DyadicAlignedPairMasks.boundary N L, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤
        (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨NR, _hNR, hR⟩ := PaperP1.AlignedSourcePairPowers.uniform_height 2 (by omega) C (ε / 2) (by positivity)
  obtain ⟨NG, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 32 2 (ε / 2) (by positivity)
  refine ⟨max NR (max NG NP), ?_⟩
  intro N hN L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg := hG N (by omega) L hcrit
  have hB : 2 ≤ (L + 1) ^ 3 := (by omega : 2 ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hpoint : ∀ xy ∈ PaperP1.DyadicAlignedPairMasks.boundary N L,
      (2 ^ pairLoss xy.1 xy.2 L : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε / 2) := by
    intro xy hxy
    have hc := (mem_filter.mp hxy).1
    rcases mem_union.mp hc with hc | hc
    · obtain ⟨hblock, hgeom⟩ := mem_filter.mp hc
      obtain ⟨hx, hy⟩ := mem_product.mp hblock
      exact hR N (by omega) L 1 2 xy.1 xy.2 hcrit (by omega) (by omega) (by norm_num)
        (by decide) (by simpa using hB) hx hy hgeom
    · obtain ⟨hblock, hgeom⟩ := mem_filter.mp hc
      obtain ⟨hx, hy⟩ := mem_product.mp hblock
      exact hR N (by omega) L 2 1 xy.1 xy.2 hcrit (by omega) (by omega) (by norm_num)
        (by decide) (by simpa using hB) hx hy hgeom
  have hc : ((PaperP1.DyadicAlignedPairMasks.boundary N L).card : ℝ) ≤ 32 * ((L + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast boundary_card N L
  have hp : 32 * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    have hh := hP N (by omega) L hg.2.2.2.2.2
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 32 * (L + 1 : ℝ) ^ 2)] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  calc
    _ ≤ ∑ _xy ∈ PaperP1.DyadicAlignedPairMasks.boundary N L, (N : ℝ) ^ (1 / 2 + ε / 2) := sum_le_sum hpoint
    _ = (PaperP1.DyadicAlignedPairMasks.boundary N L).card * (N : ℝ) ^ (1 / 2 + ε / 2) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (32 * ((L + 1 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le _)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem height_one (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ separated (channel N L 1 1) L, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicSeparatedHeightOne.uniform_power_sum (C + 1) (1 / 2) (by norm_num) (ε / 2) (by positivity)
  obtain ⟨NF, hF⟩ := double_power (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MM NF, ?_⟩
  intro N hN L hcrit
  have hsub : separated (channel N L 1 1) L ⊆ PaperP1.MacroscopicSeparatedHeightOne.pairs (2 * N) (1 / 2) L := by
    intro xy hxy
    obtain ⟨hc, hsep⟩ := mem_filter.mp hxy
    exact mem_filter.mpr ⟨channel_subset_macro (by omega : 2 ≤ N) hc, hsep⟩
  have hs : (∑ xy ∈ separated (channel N L 1 1) L, (2 ^ pairLoss xy.1 xy.2 L : ℝ)) ≤
      ∑ xy ∈ PaperP1.MacroscopicSeparatedHeightOne.pairs (2 * N) (1 / 2) L, (2 ^ pairLoss xy.1 xy.2 L : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
  have hm := hM (2 * N) (by omega) L (critical_band (by omega : 0 < N) hcrit)
  have hf : ((2 * N : ℕ) : ℝ) ^ (1 + ε / 2) ≤ (N : ℝ) ^ (1 + ε) := by
    simpa only [show (1 : ℝ) + ε / 2 + ε / 2 = 1 + ε by ring] using hF N (by omega)
  exact hs.trans (hm.trans hf)

end PaperP1.DyadicActualSectorPowers
