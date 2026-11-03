module

public import PaperP1.Asymptotics.DenseNonalignedPairsUnderBCN
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Model.InfiniteTripleCancellation

/-! # The actual joint mass of strongly intersecting locally nonaligned pairs

The pair population is ordered and uses the section-local exact-unit convention.
The existing BCN argument is the only unproved input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongNoExactPairMassUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_count (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
        ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
        θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)) →
        (P.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := DenseNonalignedPairsUnderBCN.uniform_kernel_hosts_of_no_exact
    c κ hc hBCN C θ ε hθ hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband P hP
  apply h N hN L hband P (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩)
    (fun p hp ↦ (hP p hp).2.2.1)
  intro p hp
  rw [TwoTargetEmptySource.dimension]
  exact (hP p hp).2.2.2

theorem uniform_joint_sum (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
        ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
        θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)) →
        (∑ p ∈ P, infiniteJointMoment L {p.1, p.2}) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := uniform_count c κ hc hBCN C θ (ε / 2) hθ (by positivity)
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NC + NM + NA, by omega, ?_⟩
  intro N hN L hband P hP
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hc N (by omega) L hband P hP
  have hpoint (p : ℕ × ℕ) (hp : p ∈ P) : infiniteJointMoment L {p.1, p.2} ≤ K / N := by
    have hh := MissingBlockProbabilities.infiniteJointMoment_antitone L
      (singleton_subset_iff.mpr (mem_insert_self p.1 {p.2}))
    rw [InfiniteTripleCancellation.singleton_joint] at hh
    exact hh.trans (hm N (by omega) L p.1 hband (hP p hp).1).2
  calc
    _ ≤ ∑ _p ∈ P, K / N := sum_le_sum hpoint
    _ = (P.card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (K / N) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = K * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [show -1 + ε / 2 = ε / 2 - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.StrongNoExactPairMassUnderBCN
