module

public import PaperP1.Asymptotics.AllPairRankUnderBCN
public import PaperP1.Model.TripleRankGeometry

/-! # The stronger nonaligned probability exponent and every containing family

The same explicit BCN argument is the only unformalized input. The gap
between its rank coefficient and one half is retained numerically.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedJointProbabilityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AllPairRankUnderBCN
  PaperP1.TripleRankGeometry PaperP1.FreeComponentRank PaperP1.CriticalRankMass

def rankSlope : ℝ := (2 / 3) * Real.log 2

def tripleGap : ℝ := 1 / 2 - rankSlope

theorem rankSlope_pos : 0 < rankSlope := by
  unfold rankSlope
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

theorem tripleGap_pos : 0 < tripleGap := by
  unfold tripleGap rankSlope
  linarith only [ShortBasisCurveScale.rank_threshold_lt_half]

theorem tripleGap_lt_half : tripleGap < 1 / 2 := by
  unfold tripleGap
  linarith only [rankSlope_pos]

theorem uniform_pair_probability (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
      infiniteJointMoment L {x, y} ≤ (N : ℝ) ^ (-2 + rankSlope + ε) := by
  obtain ⟨NR, hrank⟩ := nonaligned_pair_bound c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NM, hmarg⟩ := critical_nominal_marginal_cap C
  obtain ⟨NP, hmass⟩ := critical_rankMass_coefficient_bound C rankSlope ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NR (max NM (max NP NG))), by omega, ?_⟩
  intro N hN L x y hband hx hy hxy hnon
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hf := pair_joint_le_rank_mass x y L hxy hL
    (hmarg N (by omega) L hband x hx) (hmarg N (by omega) L hband y hy)
  change infiniteJointMoment L {x, y} ≤ rankMass L (pairIntersectionRank x y L) at hf
  have hr : (pairIntersectionRank x y L : ℝ) ≤ (rankSlope + ε / 2) * L :=
    hrank N (by omega) L x y hband hx hy hnon
  have hp := hf.trans (hmass N (by omega) L (pairIntersectionRank x y L) hband hr)
  simpa only [show rankSlope - 2 + ε = -2 + rankSlope + ε by ring] using hp

theorem uniform_family_probability (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
      infiniteJointMoment L I ≤ (N : ℝ) ^ (-2 + rankSlope + ε) := by
  obtain ⟨N₀, hN₀, hpair⟩ := uniform_pair_probability c κ hc hBCN C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband I hI x hx y hy hxy hnon
  have hsub : ({x, y} : Finset ℕ) ⊆ I := by
    intro z hz
    obtain rfl | hz := mem_insert.mp hz
    · exact hx
    · simpa only [mem_singleton.mp hz] using hy
  exact (infiniteJointMoment_antitone L hsub).trans
    (hpair N hN L x y hband (hI hx) (hI hy) hxy hnon)

end PaperP1.NonalignedJointProbabilityUnderBCN
