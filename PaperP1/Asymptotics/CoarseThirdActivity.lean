module

public import PaperP1.Asymptotics.CoarseConnectedTripleMass
public import PaperP1.Asymptotics.SharpThirdCancellation
public import PaperP1.Model.CompatibleTripleJointBound

/-! # The full actual third activity and cumulant have unconditional power one

The sharper source power 41/30 is not asserted by this coarse estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseThirdActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TripleActivityConnected
  PaperP1.ThirdRunFactorialCumulant

theorem uniform_positive (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      positiveConnected L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NJ, _hNJ, hj⟩ := CoarseConnectedTripleMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 8 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NJ + NG + NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let F := (G.powersetCard 3).filter fun I ↦
    ConnectedWindowFamilies.Connected L I ∧ 0 < infiniteJointMoment L I
  have hF : F ⊆ ConnectedWindowFamilies.connectedFamilies G L 3 := by
    intro I hI
    have hh := mem_filter.mp hI
    exact mem_filter.mpr ⟨hh.1, hh.2.1⟩
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : infiniteCenteredCoefficient L I ≤ 8 * infiniteJointMoment L I := by
    have hd := mem_filter.mp hI
    have hcard := (mem_powersetCard.mp hd.1).2
    have hh := CompatibleTripleJointBound.centered_compatible_bound L I hL hd.2.2
    norm_num only [hcard, Nat.reducePow, Nat.cast_ofNat] at hh
    exact (le_abs_self _).trans hh
  calc
    _ ≤ ∑ I ∈ F, 8 * infiniteJointMoment L I := sum_le_sum hpoint
    _ = 8 * ∑ I ∈ F, infiniteJointMoment L I := by rw [mul_sum]
    _ ≤ 8 * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left
      (hj N (by omega) L hband G hG F hF) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_absolute (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := uniform_positive C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := SharpThirdCancellation.uniform_cancellation C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NP + NC + NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpG := hp N (by omega) L hband G hG
  have hcG := (hc N (by omega) L hband G hG).2.2.1
  have hsmall : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  linarith only [hpG, hcG, hsmall, hfactor]

theorem uniform_cumulant (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |thirdFactorialCumulant G L| ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NP, _hNP, hp⟩ := uniform_positive C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := SharpThirdCancellation.uniform_cancellation C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 7 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NP + NC + NG + NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hpG := hp N (by omega) L hband G hG
  have hcG := (hc N (by omega) L hband G hG).2.2.2.1
  have hK : 0 ≤ positiveConnected L (G.powersetCard 3) :=
    sum_nonneg fun I hI ↦ CompatibleRunCentered.coefficient_nonneg L I hL (mem_filter.mp hI).2.2
  have htriangle : |thirdFactorialCumulant G L| ≤
      |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| +
        6 * positiveConnected L (G.powersetCard 3) := by
    have hh := abs_add_le (thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3))
      (6 * positiveConnected L (G.powersetCard 3))
    have hsix : 0 ≤ 6 * positiveConnected L (G.powersetCard 3) := mul_nonneg (by norm_num) hK
    simpa only [sub_add_cancel, abs_of_nonneg hsix] using hh
  have hsmall : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hfactor : 7 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  linarith only [hpG, hcG, htriangle, hsmall, hfactor]

end PaperP1.CoarseThirdActivity
