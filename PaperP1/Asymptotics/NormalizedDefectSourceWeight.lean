module

public import PaperP1.Asymptotics.AlignedSourcePairPowers
public import PaperP1.Asymptotics.NormalizedDefectPairActivity
public import PaperP1.Model.SourcePairPositiveWeight

/-! # Nonprivate fixed-channel arithmetic weights are small even for incompatible pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedDefectSourceWeight

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedDefectSources
  PaperP1.NormalizedDefectPairActivity PaperP1.SourcePairPositiveWeight

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_source_mass (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (∑ xy ∈ badSources N H a b L, weight xy.1 xy.2 L) ≤
        (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := AlignedSourcePairPowers.uniform_height b (ha.trans hab) C (ε / 2) (by positivity)
  obtain ⟨NC, hc⟩ := NormalizedDefectSourceCount.bad_sources_rate C D a b ha (ha.trans hab) hab.le (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max b 2)
  refine ⟨max 2 (max NP (max NC NG)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgeom := hg N (by omega) L hband
  have hheight : max a b ≤ (L + 1) ^ 3 := by
    rw [max_eq_right hab.le]
    exact (by omega : b ≤ L + 1).trans (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hcap : ∀ xy ∈ badSources N H a b L, weight xy.1 xy.2 L ≤ (N : ℝ) ^ (1 / (b : ℝ) + ε / 2) := by
    intro xy hxy
    have hu := bad_subset_units N H a b L hxy
    obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hxy).1
    have halign : EnlargedPairGeometry.Geometric a b xy.1 xy.2 L := by
      simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using
        FixedChannelLinearCount.unit_alignment (by omega : 0 < N) hu
    have hpower := hp N (by omega) L a b xy.1 xy.2 hband ha (ha.trans hab) hcop
      (by rw [max_eq_right hab.le]) hheight hx hy halign
    exact (sub_le_self _ zero_le_one).trans hpower
  calc
    _ ≤ ∑ _xy ∈ badSources N H a b L, (N : ℝ) ^ (1 / (b : ℝ) + ε / 2) := sum_le_sum hcap
    _ = ((badSources N H a b L).card : ℝ) * (N : ℝ) ^ (1 / (b : ℝ) + ε / 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 / 2 + ε / 2) * (N : ℝ) ^ (1 / (b : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L H hband hcut hH) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_pair_mass (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (∑ e ∈ pairs N H a b L, setWeight L e) ≤
        (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NS, _hNS, hs⟩ := uniform_source_mass C ε D a b ha hab hcop hε
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max 2 (max NS NL), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hsum : (∑ xy ∈ badSources N H a b L, setWeight L {xy.1, xy.2}) =
      ∑ xy ∈ badSources N H a b L, weight xy.1 xy.2 L := by
    apply sum_congr rfl
    intro xy hxy
    exact setWeight_pair (ne_of_lt (PairLossWeights.unit_order (by omega : 0 < N) hab hlarge
      (bad_subset_units N H a b L hxy))) L
  calc
    _ ≤ ∑ xy ∈ badSources N H a b L, setWeight L {xy.1, xy.2} :=
      sum_image_le_of_nonneg (f := setWeight L) (fun e _ ↦ setWeight_nonneg L e)
    _ = ∑ xy ∈ badSources N H a b L, weight xy.1 xy.2 L := hsum
    _ ≤ _ := hs N (by omega) L H hband hcut hH

end PaperP1.NormalizedDefectSourceWeight
