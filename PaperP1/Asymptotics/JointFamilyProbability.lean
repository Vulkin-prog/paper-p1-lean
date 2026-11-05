module

public import PaperP1.Asymptotics.AllPairRank
public import PaperP1.Asymptotics.JointFamilyProbabilityUnderBCN
public import PaperP1.Model.TripleRankGeometry
public import Mathlib.Data.Finset.Fold

/-! # Actual joint-probability bounds for every family containing a distinct pair

All actual windows, critical-band quantifiers and zero-probability cases are
retained. The height-controlled rank proof supplies the former BCN use.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointFamilyProbability

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FreeComponentRank
  PaperP1.TripleRankGeometry PaperP1.AllPairRank PaperP1.CriticalRankMass

open JointFamilyProbabilityUnderBCN (maximalTripleProbability)

theorem uniform_pair_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      x ≠ y → infiniteJointMoment L {x, y} ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨Npair, hpair⟩ := compatible_pair_bound C (ε / 2) (by positivity)
  obtain ⟨Nmarg, hmarg⟩ := critical_nominal_marginal_cap C
  obtain ⟨Nmass, hmass⟩ := critical_rankMass_bound C ε hε
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max Npair (max Nmarg (max Nmass Ngeom)), ?_⟩
  intro N hN L x y hband hx hy hxy
  obtain ⟨_hNtwo, hBtwo, _⟩ := hgeom N (by omega) L hband
  have hL : 0 < L := by omega
  by_cases hq : 0 < infiniteJointMoment L {x, y}
  · have hrank := hpair N (by omega) L x y hband hx hy hxy hq
    have hfinite := pair_joint_le_rank_mass x y L hxy hL
      (hmarg N (by omega) L hband x hx) (hmarg N (by omega) L hband y hy)
    change infiniteJointMoment L {x, y} ≤ rankMass L (pairIntersectionRank x y L) at hfinite
    exact hfinite.trans (hmass N (by omega) L (pairIntersectionRank x y L) hband hrank)
  · exact (le_of_not_gt hq).trans (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem uniform_family_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      2 ≤ I.card → infiniteJointMoment L I ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := uniform_pair_probability C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband I hI hcard
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < I.card)
  have hpair := hN₀ N hN L x y hband (hI hx) (hI hy) hxy
  have hsub : ({x, y} : Finset ℕ) ⊆ I := by
    intro w hw
    obtain rfl | hw := mem_insert.mp hw
    · exact hx
    · simpa only [mem_singleton.mp hw] using hy
  exact (infiniteJointMoment_antitone L hsub).trans hpair

theorem uniform_triple_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      I.card = 3 → infiniteJointMoment L I ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := uniform_family_probability C ε hε
  exact ⟨N₀, fun N hN L hband I hI hcard ↦ hN₀ N hN L hband I hI (by omega)⟩

theorem uniform_maximal_triple_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        maximalTripleProbability N L ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := uniform_triple_probability C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  apply (Finset.fold_max_le _).mpr
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg N) _, ?_⟩
  intro I hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hI
  exact hN₀ N hN L hband I hsub hcard

end PaperP1.JointFamilyProbability
