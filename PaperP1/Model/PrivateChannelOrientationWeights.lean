module

public import PaperP1.Model.CompatibleChannelEdges

/-! # Every source observable retains the exact two ordered orientations

Zero-probability pairs remain in the symmetric geometric family. They
contribute zero to every actual source-weighted conditional expression.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelOrientationWeights

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateChannelSources

theorem symmetric_sum {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (f : Finset ℕ → ℝ) :
    (∑ xy ∈ channelSources N H a b L, f {xy.1, xy.2}) =
      2 * ∑ e ∈ PrivateChannelActivity.pairs N H a b L, f e := by
  classical
  rw [channelSources, sum_union (orientation_disjoint hN hab hlarge), sum_image]
  · have hs : (∑ xy ∈ goodSources N H a b L, f {xy.2, xy.1}) =
        ∑ xy ∈ goodSources N H a b L, f {xy.1, xy.2} := by
      exact sum_congr rfl (fun xy _ ↦ congrArg f (pair_comm xy.2 xy.1))
    rw [PrivateChannelActivity.pairs, sum_image (PrivateChannelActivity.pair_map_injective hN hab hlarge)]
    change (∑ xy ∈ goodSources N H a b L, f {xy.1, xy.2}) +
      (∑ xy ∈ goodSources N H a b L, f {xy.2, xy.1}) = _
    rw [hs]
    ring
  · intro xy _ uv _ heq
    have hh := congrArg Prod.swap heq
    simpa using hh

theorem compatible_weighted_sum {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (f : Finset ℕ → ℝ) :
    (∑ xy ∈ channelSources N H a b L, infiniteJointMoment L {xy.1, xy.2} * f {xy.1, xy.2}) =
      2 * ∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e * f e := by
  classical
  rw [symmetric_sum hN hab hlarge (fun e ↦ infiniteJointMoment L e * f e)]
  congr 1
  symm
  apply sum_subset (filter_subset _ _)
  intro e he hnot
  have hzero : infiniteJointMoment L e = 0 := by
    apply le_antisymm _ (infiniteJointMoment_nonneg L e)
    exact not_lt.mp (fun hp ↦ hnot (mem_filter.mpr ⟨he, hp⟩))
  rw [hzero, zero_mul]

theorem normalized_weighted_sum {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (f : Finset ℕ → ℝ) :
    (∑ xy ∈ channelSources N H a b L, infiniteJointMoment L {xy.1, xy.2} * f {xy.1, xy.2}) /
        channelMass N H a b L =
      (∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e * f e) /
        (∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e) := by
  rw [compatible_weighted_sum hN hab hlarge]
  have hh := CompatibleChannelEdges.joint_mass_eq (H := H) hN hab hlarge
  have hmass : channelMass N H a b L = 2 * ∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e := by
    linarith only [hh]
  rw [hmass, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

end PaperP1.PrivateChannelOrientationWeights
