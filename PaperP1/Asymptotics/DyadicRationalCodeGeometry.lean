module

public import PaperP1.Arithmetic.DyadicAlignedPairMasks
public import PaperP1.Asymptotics.MacroscopicRationalCodeGeometry

/-! # The canonical global rational code on the actual dyadic roots

No dyadic channel or mass input is assumed. Exact interval transport
instantiates the proved moving-height canonical code identification.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicRationalCodeGeometry

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.EnlargedPairGeometry
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.DyadicAlignedPairMasks PaperP1.DyadicMacroscopicTransfer

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem high_of_macro {N L q : ℕ} {xy : ℕ × ℕ} (hx : xy.1 ∈ dyadicBlock N) (hy : xy.2 ∈ dyadicBlock N)
    (hh : xy ∈ PaperP1.MacroscopicHighRelationMass.highPairs (2 * N) (1 / 2) L q) : xy ∈ high N L q := by
  obtain ⟨ab, hab, hpair⟩ := mem_biUnion.mp hh
  exact mem_biUnion.mpr ⟨ab, hab, mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, (mem_filter.mp hpair).2⟩⟩

theorem uniform_geometry (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < L ∧ ∀ x ∈ dyadicBlock N, L + 1 < x ∧ 4 * (L + 1) ^ 7 < x := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_geometry (C + 1) (1 / 2) (by norm_num)
  refine ⟨MM, ?_⟩
  intro N hN L hcrit
  obtain ⟨hL, hroot⟩ := hM (2 * N) (by omega) L (critical_band (by omega : 0 < N) hcrit)
  exact ⟨hL, fun x hx ↦ hroot x (dyadic_subset (by omega : 2 ≤ N) hx)⟩

theorem uniform_channel (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      Geometric a b x y L →
      PaperP1.RationalUnitCode.nullity x y L = (units a b x y L).card - 1 ∧
      PaperP1.RationalUnitCode.weight x y L ≤ (2 ^ pairLoss x y L : ℝ) - 1 := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_channel (C + 1) (1 / 2) (by norm_num)
  refine ⟨MM, ?_⟩
  intro N hN L hcrit x hx y hy a b ha hb hab haB hbB hg
  exact hM (2 * N) (by omega) L (critical_band (by omega : 0 < N) hcrit)
    x (dyadic_subset (by omega : 2 ≤ N) hx) y (dyadic_subset (by omega : 2 ≤ N) hy) a b ha hb hab haB hbB hg

theorem uniform_off_channel (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      (x, y) ∉ high N L 1 →
      PaperP1.RationalUnitCode.nullity x y L = 0 ∧ PaperP1.RationalUnitCode.weight x y L = 0 := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicRationalCodeGeometry.uniform_off_channel (C + 1) (1 / 2) (by norm_num)
  refine ⟨MM, ?_⟩
  intro N hN L hcrit x hx y hy hn
  exact hM (2 * N) (by omega) L (critical_band (by omega : 0 < N) hcrit)
    x (dyadic_subset (by omega : 2 ≤ N) hx) y (dyadic_subset (by omega : 2 ≤ N) hy)
    (fun hh ↦ hn (high_of_macro hx hy hh))

theorem uniform_aligned_bound (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ xy ∈ aligned N L,
      PaperP1.RationalUnitCode.weight xy.1 xy.2 L ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 := by
  obtain ⟨N₀, h⟩ := uniform_channel C
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit xy hxy
  obtain ⟨hh, _hsep⟩ := mem_filter.mp hxy
  obtain ⟨⟨a, b⟩, hab, hpair⟩ := mem_biUnion.mp hh
  obtain ⟨hcoeff, _hq, hcop⟩ := mem_filter.mp hab
  obtain ⟨haI, hbI⟩ := mem_product.mp hcoeff
  obtain ⟨ha1, haB⟩ := mem_Icc.mp haI
  obtain ⟨hb1, hbB⟩ := mem_Icc.mp hbI
  obtain ⟨hblock, hg⟩ := mem_filter.mp hpair
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact (h N hN L hcrit xy.1 hx xy.2 hy a b (by omega) (by omega) hcop haB hbB hg).2

end PaperP1.DyadicRationalCodeGeometry
