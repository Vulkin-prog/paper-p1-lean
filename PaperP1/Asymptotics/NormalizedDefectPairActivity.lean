module

public import PaperP1.Asymptotics.UnitChannelPairWeights
public import PaperP1.Asymptotics.NormalizedDefectSourceCount

/-! # The actual nonprivate fixed-channel class has activity N^(-3/2+1/b+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedDefectPairActivity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedDefectSources PaperP1.FixedChannelSourceGeometry

def pairs (N H a b L : ℕ) : Finset (Finset ℕ) :=
  (badSources N H a b L).image fun xy ↦ {xy.1, xy.2}

theorem bad_subset_units (N H a b L : ℕ) : badSources N H a b L ⊆ unitSources N a b L := by
  classical
  intro xy hxy
  obtain ⟨hxy, hu, _⟩ := mem_filter.mp hxy
  exact mem_filter.mpr ⟨hxy, hu⟩

theorem uniform_activity (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      CompatibleActivitySplit.absolute L (pairs N H a b L) ≤ (N : ℝ) ^ (-3 / 2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NW, _hNW, hw⟩ := UnitChannelPairWeights.uniform_coefficient C (ε / 2) a b ha hab hcop (by positivity)
  obtain ⟨NC, hc⟩ := NormalizedDefectSourceCount.bad_sources_rate C D a b ha (ha.trans hab) hab.le (ε / 2) (by positivity)
  refine ⟨max 2 (max NW NC), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ xy ∈ badSources N H a b L, |infiniteCenteredCoefficient L {xy.1, xy.2}| :=
      sum_image_le_of_nonneg (f := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|) (fun e _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))
    _ ≤ ∑ _xy ∈ badSources N H a b L, (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      sum_le_sum fun xy hxy ↦ hw N (by omega) L hband xy (bad_subset_units N H a b L hxy)
    _ = ((badSources N H a b L).card : ℝ) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 / 2 + ε / 2) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L H hband hcut hH) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_joint_mass (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (∑ e ∈ pairs N H a b L, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-3 / 2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NW, _hNW, hw⟩ := UnitChannelPairWeights.uniform_joint C (ε / 2) a b ha hab hcop (by positivity)
  obtain ⟨NC, hc⟩ := NormalizedDefectSourceCount.bad_sources_rate C D a b ha (ha.trans hab) hab.le (ε / 2) (by positivity)
  refine ⟨max 2 (max NW NC), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ xy ∈ badSources N H a b L, infiniteJointMoment L {xy.1, xy.2} :=
      sum_image_le_of_nonneg (fun e _ ↦ infiniteJointMoment_nonneg L e)
    _ ≤ ∑ _xy ∈ badSources N H a b L, (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      sum_le_sum fun xy hxy ↦ hw N (by omega) L hband xy (bad_subset_units N H a b L hxy)
    _ = ((badSources N H a b L).card : ℝ) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 / 2 + ε / 2) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L H hband hcut hH) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.NormalizedDefectPairActivity
