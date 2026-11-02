module

public import PaperP1.Model.BoundaryAlignedPairs
public import PaperP1.Asymptotics.ZeroUnitAlignedActivity
public import PaperP1.Asymptotics.FixedContactCenteredActivity
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The height-one/two enlarged aligned boundary has only N^(-1+epsilon) activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundaryAlignedActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.BoundaryAlignedPairs

theorem height_one (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (channel N L 1 1) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := FixedContactCenteredActivity.uniform_bound 2 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NZ, _hNZ, hz⟩ := ZeroUnitAlignedActivity.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NZ NF)), by omega, ?_⟩
  intro N hN L hband
  have hsub : ClosePairs.pairs (dyadicBlock N) L ⊆ ContactCenteredTruncation.families (dyadicBlock N) L 2 := by
    intro e he
    exact mem_filter.mpr ⟨ClosePairs.subset (dyadicBlock N) L he, e, he, subset_refl _⟩
  have hclose : CompatibleActivitySplit.absolute L (ClosePairs.pairs (dyadicBlock N) L) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ abs_nonneg _)).trans
      (hc N (by omega) L hband (dyadicBlock N) (subset_refl _))
  calc
    _ ≤ CompatibleActivitySplit.absolute L (ClosePairs.pairs (dyadicBlock N) L) +
        CompatibleActivitySplit.absolute L (AlignedChannelFamilies.zeroFamilies N L) :=
      ActivityFamilyCover.two_families L _ _ _ (fun _ he _ ↦ height_one_cover (by omega : 2 ≤ N) he)
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by
      have hzero := hz N (by omega) L hband
      linarith only [hclose, hzero]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem height_two (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ channel N L 1 2, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-1 + ε) ∧
        CompatibleActivitySplit.absolute L (channel N L 1 2) ≤ (N : ℝ) ^ (-1 + ε) := by
  let K := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NL, hl⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (16 * K * CriticalBandScale.upperScale ^ 2) 2 ε hε
  refine ⟨max 2 (max NP (max NS NL)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : 16 * K * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ 16 * K * (CriticalBandScale.upperScale * Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) (by positivity)
      _ = (16 * K * CriticalBandScale.upperScale ^ 2) * (Real.log N) ^ 2 := by ring
      _ ≤ _ := by simpa only [Real.rpow_two] using hl N (by omega)
  have hsum (w : Finset ℕ → ℝ) (hcap : ∀ e ∈ channel N L 1 2, w e ≤ K / N) :
      (∑ e ∈ channel N L 1 2, w e) ≤ (N : ℝ) ^ (-1 + ε) := by
    calc
      _ ≤ ∑ _e ∈ channel N L 1 2, K / N := sum_le_sum hcap
      _ = ((channel N L 1 2).card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (16 * ((L + 1 : ℕ) : ℝ) ^ 2) * (K / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast height_two_card N L) (div_nonneg hK hn.le)
      _ = (16 * K * ((L + 1 : ℕ) : ℝ) ^ 2) / N := by ring
      _ ≤ (N : ℝ) ^ ε / N := div_le_div_of_nonneg_right hpoly hn.le
      _ = _ := by rw [show -1 + ε = ε - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
  constructor
  · apply hsum
    intro e he
    obtain ⟨x, y, hx, _hy, rfl, _hxy, _hg⟩ := data he
    have hmono : infiniteJointMoment L {x, y} ≤ infiniteMarginal x L := by
      simpa only [InfiniteTripleCancellation.singleton_joint] using
        MissingBlockProbabilities.infiniteJointMoment_antitone L (singleton_subset_iff.mpr (mem_insert_self x {y}))
    exact hmono.trans (hp N (by omega) L hband x hx)
  · apply hsum
    intro e he
    obtain ⟨x, y, hx, _hy, rfl, hxy, _hg⟩ := data he
    exact (PairRowActivity.pair_absolute_le_marginal L x y hxy.ne).trans (hp N (by omega) L hband x hx)

end PaperP1.BoundaryAlignedActivity
