module

public import PaperP1.Model.NonalignedActivityHostCap
public import PaperP1.Asymptotics.NonalignedJointProbabilityUnderBCN

/-! # Retain the strict rank gap in the actual nonaligned activity estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedActivityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NonalignedJointProbabilityUnderBCN

theorem uniform_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
        (N : ℝ) ^ (-1 + rankSlope + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := OriginalPairHosts.uniform_count C (ε / 4) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := uniform_pair_probability c κ hc hBCN C (ε / 4) (by positivity)
  obtain ⟨NI, hi⟩ := PairHostIndependentMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + rankSlope + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NH (max NP (max NI (max NG NF)))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hfinite := NonalignedActivityHostCap.finite_bound (by omega : 2 ≤ N) hL
    (Real.rpow_nonneg hn.le (-2 + rankSlope + ε / 4))
    (fun x hx y hy hxy hnon ↦ hp N (by omega) L x y hband hx hy hxy.ne hnon)
  have hproduct : ((PairHostCover.hosts N L).card : ℝ) *
      (N : ℝ) ^ (-2 + rankSlope + ε / 4) ≤ (N : ℝ) ^ (-1 + rankSlope + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (1 + ε / 4) * (N : ℝ) ^ (-2 + rankSlope + ε / 4) :=
        mul_le_mul_of_nonneg_right (hh N (by omega) L hband) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hind : PairHostIndependentMass.mass N L ≤ (N : ℝ) ^ (-1 + rankSlope + ε / 2) :=
    (hi N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [rankSlope_pos]))
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + rankSlope + ε / 2) := by
      linarith only [hfinite, hproduct, hind]
    _ ≤ (N : ℝ) ^ ((-1 + rankSlope + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NonalignedActivityUnderBCN
