module

public import PaperP1.Model.OnceAllOriginalCoupling
public import PaperP1.Model.AllPairCountMeans
public import PaperP1.Probability.FirstWassersteinFinite

/-! # The original once/all coupling is optimal for first Wasserstein distance

The exact distance is the difference of the genuine count means. This is
unconditional, for every cutoff and edge-height parameter. No sharp arithmetic
second-moment estimate is required for the identity or for optimality.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OnceAllMeanCost

open MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalCountProjection PaperP1.OnceAllOriginalCoupling

theorem wasserstein_eq_mean_gap (H : ℝ) (N L : ℕ) :
    wasserstein H N L = OnceErasedCount.countMean H N L - AllPairCountMeans.goodMean H N L := by
  let S := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  let M := PositionalObservationLaw.cutoff S L
  let P := cylinderProbability M
  let J := fun x ↦ startIndicator (M := M) x L
  let Z := FiniteOnceAllCoupling.onceObservation S J E
  let W := FiniteOnceAllCoupling.allObservation S J E
  have hZW : ∀ ω, W ω ≤ Z ω := fun ω ↦
    (one_all_count_cost E (configuration S J ω) (PositionalDeletedFields.configuration_binary S J ω)
      (fun e he ↦ RetainedGoodEdges.good_pair_card H N L e he)).1
  have hh := FirstWassersteinFinite.ordered_distance_eq P Z W hZW
  have hZ : OnceErasedCount.countMean H N L = finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) := by
    unfold OnceErasedCount.countMean
    rw [OnceErasedCount.law_eq_observation]
    exact FiniteObservationLaw.integral_eq _ _ _
  have hW : AllPairCountMeans.goodMean H N L = finiteExpectation P.weight (fun ω ↦ (W ω : ℝ)) :=
    FiniteObservationLaw.integral_eq _ _ _
  rw [hZ, hW]
  unfold wasserstein FirstWasserstein.distance
  rw [OnceErasedCount.law_eq_observation]
  exact hh

theorem mean_ordered (H : ℝ) (N L : ℕ) :
    AllPairCountMeans.goodMean H N L ≤ OnceErasedCount.countMean H N L := by
  have hh := wasserstein_nonneg H N L
  rw [wasserstein_eq_mean_gap] at hh
  exact sub_nonneg.mp hh

theorem totalVariation_le_mean_gap (H : ℝ) (N L : ℕ) :
    totalVariation H N L ≤ OnceErasedCount.countMean H N L - AllPairCountMeans.goodMean H N L := by
  calc
    _ ≤ wasserstein H N L := FirstWassersteinTests.totalVariation_le_distance
      (OnceErasedCount.law H N L) (AllPairOriginalLaws.goodLaw H N L) ⟨goodPlan H N L⟩
    _ = _ := wasserstein_eq_mean_gap H N L

end PaperP1.OnceAllMeanCost
