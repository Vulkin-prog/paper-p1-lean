module

public import PaperP1.Asymptotics.RetainedBadPairActivityUnderInputs
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Model.SecondFactorialCorrection

/-! # The actual retained joint pair parameter and the full regular covariance agree at rate four-fifths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedBetaCovarianceUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedReferenceTheorem
  PaperP1.RetainedBoundaryPositiveMass PaperP1.SecondFactorialCorrection PaperP1.FinitePairDeficitInputs

theorem independent_bound (H : ℝ) (N L : ℕ) (hN : 2 ≤ N) :
    (∑ e ∈ GoodEdgeCompression.goodEdges H N L, ∏ x ∈ e, infiniteMarginal x L) ≤
      PrivateChannelActivity.independentMass N 0 2 3 L + PrivateChannelActivity.independentMass N 0 3 4 L := by
  have hsub := RetainedIndependentDeficitComparison.good_subset_zero_channels (L := L) hN H
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ prod_nonneg fun x _ ↦
    MissingBlockProbabilities.infiniteMarginal_nonneg x L)).trans
    (GraphStarWeights.sum_union_le_nonneg _ _ (fun e ↦ ∏ x ∈ e, infiniteMarginal x L)
      (fun _e ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem uniform_independent (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      (∑ e ∈ GoodEdgeCompression.goodEdges H N L, ∏ x ∈ e, infiniteMarginal x L) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N23, _hN23, h23⟩ := PrivateChannelActivityRate.uniform_independent_mass C (ε / 2) 2 3
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨N34, _hN34, h34⟩ := PrivateChannelActivityRate.uniform_independent_mass C (ε / 2) 3 4
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + N23 + N34 + NF, by omega, ?_⟩
  intro N hN L hband H
  have h := independent_bound H N L (by omega)
  have h23 := h23 N (by omega) L 0 hband
  have h34 := h34 N (by omega) L 0 hband
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [h, h23, h34]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem finite_bound (H : ℝ) (N L : ℕ) (hN : 2 ≤ N) :
    |beta H N L - regularCovariance N L| ≤
      (∑ e ∈ GoodEdgeCompression.goodEdges H N L, ∏ x ∈ e, infiniteMarginal x L) + badActivity H N L / 4 := by
  classical
  let E := GoodEdgeCompression.goodEdges H N L
  let G := RegularStarts.regularStarts N L
  have hsplit := sum_sdiff (good_subset H N L hN) (f := infiniteCenteredCoefficient L)
  change (∑ e ∈ G.powersetCard 2 \ E, infiniteCenteredCoefficient L e) + (∑ e ∈ E, infiniteCenteredCoefficient L e) =
    ∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e at hsplit
  have hgood : (∑ e ∈ E, infiniteJointMoment L e) =
      (∑ e ∈ E, infiniteCenteredCoefficient L e) + ∑ e ∈ E, ∏ x ∈ e, infiniteMarginal x L := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e he
    rw [CompressedJointMoments.centered_pair L e (RetainedGoodEdges.good_pair_card H N L e he)]
    ring
  have hgap : beta H N L - regularCovariance N L =
      (∑ e ∈ E, ∏ x ∈ e, infiniteMarginal x L) -
        ∑ e ∈ G.powersetCard 2 \ E, infiniteCenteredCoefficient L e := by
    change (∑ e ∈ E, infiniteJointMoment L e) - (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) = _
    linarith only [hsplit, hgood]
  rw [hgap]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sum_nonneg fun e _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]
  have h := abs_sum_le_sum_abs (fun e ↦ infiniteCenteredCoefficient L e) (G.powersetCard 2 \ E)
  have heq : badActivity H N L / 4 = ∑ e ∈ G.powersetCard 2 \ E, |infiniteCenteredCoefficient L e| := by
    unfold badActivity
    ring
  rw [heq]
  exact add_le_add le_rfl h

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 256)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |beta (8 * (L + 1) : ℕ) N L - regularCovariance N L| ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := RetainedBadPairActivityUnderInputs.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NI, _hNI, hi⟩ := uniform_independent C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hs : (ε / 2) / 128 = ε / 256 := by ring
  obtain ⟨NB, _hNB, hb⟩ := hp (by simpa only [hs] using hgeo)
  refine ⟨10 + NB + NI + NF, by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hI := (hi N (by omega) L hband (8 * (L + 1) : ℕ)).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have hB := hb N (by omega) L hband
  have hP := Real.rpow_nonneg (Nat.cast_nonneg N) (-4 / 5 + ε / 2)
  have h := finite_bound (8 * (L + 1) : ℕ) N L (by omega)
  calc
    _ ≤ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [h, hI, hB, hP]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RetainedBetaCovarianceUnderInputs
