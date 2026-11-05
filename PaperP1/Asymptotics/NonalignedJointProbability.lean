module

public import PaperP1.Asymptotics.AllPairRank
public import PaperP1.Asymptotics.NonalignedJointProbabilityUnderBCN
public import PaperP1.Model.TripleRankGeometry

/-! # The internal stronger nonaligned probability exponent

All actual windows, critical-band quantifiers and zero-probability cases are
retained. The height-controlled rank proof supplies the former BCN use.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedJointProbability

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AllPairRank
  PaperP1.TripleRankGeometry PaperP1.FreeComponentRank PaperP1.CriticalRankMass

open NonalignedJointProbabilityUnderBCN (rankSlope tripleGap)

theorem uniform_pair_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
      infiniteJointMoment L {x, y} ≤ (N : ℝ) ^ (-2 + rankSlope + ε) := by
  obtain ⟨NR, hrank⟩ := nonaligned_pair_bound C (ε / 2) (by positivity)
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

theorem uniform_family_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
      infiniteJointMoment L I ≤ (N : ℝ) ^ (-2 + rankSlope + ε) := by
  obtain ⟨N₀, hN₀, hpair⟩ := uniform_pair_probability C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband I hI x hx y hy hxy hnon
  have hsub : ({x, y} : Finset ℕ) ⊆ I := by
    intro z hz
    obtain rfl | hz := mem_insert.mp hz
    · exact hx
    · simpa only [mem_singleton.mp hz] using hy
  exact (infiniteJointMoment_antitone L hsub).trans
    (hpair N hN L x y hband (hI hx) (hI hy) hxy hnon)

end PaperP1.NonalignedJointProbability
