module

public import PaperP1.Model.AllPairCountMeans
public import PaperP1.Probability.PositionalCountCumulant
public import PaperP1.Probability.PositionalCountReference
public import PaperP1.Arithmetic.FiniteChannelHierarchy

/-! # Exact mean and independent-background parameters of the erased count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ErasedCountReference

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalCountProjection PaperP1.PositionalDeletedFields
  PaperP1.PositionalFactorialCovariance PaperP1.AllPairCountMeans

def singleMean (H : ℝ) (N L : ℕ) : ℝ :=
  FiniteChannelHierarchy.nominalMean N L - 2 * RetainedReferenceTheorem.beta H N L

theorem singleMean_eq_sum {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    singleMean H N L = ∑ x ∈ dyadicBlock N, ((2 ^ L : ℝ)⁻¹ -
      PositionalCompoundPoisson.incidence (GoodEdgeCompression.goodEdges H N L) (infiniteJointMoment L) x) := by
  rw [sum_sub_distrib, PositionalCountReference.sum_incidence _ _ _
    (fun e he ↦ ⟨(RetainedGoodEdges.good_pair_regular hN e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he⟩),
    sum_const, nsmul_eq_mul, dyadicBlock_card]
  rfl

theorem singleMean_le_nominal (H : ℝ) (N L : ℕ) :
    singleMean H N L ≤ FiniteChannelHierarchy.nominalMean N L := by
  have hβ : 0 ≤ RetainedReferenceTheorem.beta H N L :=
    sum_nonneg (fun e _he ↦ infiniteJointMoment_nonneg L e)
  unfold singleMean
  linarith only [hβ]

theorem goodMean_eq_sum (H : ℝ) (N L : ℕ) :
    goodMean H N L = ∑ x ∈ dyadicBlock N, mean
      (isolatedLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L) x := by
  let S := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  let M := PositionalObservationLaw.cutoff S L
  let P := cylinderProbability M
  let J := fun x ↦ startIndicator (M := M) x L
  have hmean (x : ℕ) : mean (isolatedLaw E S L) x =
      finiteExpectation P.weight (fun ω ↦ (isolate E (configuration S J ω) x : ℝ)) := by
    have hh := FiniteDeletedIntensity.mean_isolated P S J E x
    simp only [← PositionalDeletionIntensity.isolate_coordinate] at hh
    convert hh using 1
    congr!
  calc
    _ = finiteExpectation P.weight (fun ω ↦ (totalCount (isolate E (configuration S J ω)) : ℝ)) :=
      FiniteObservationLaw.integral_eq _ _ _
    _ = finiteExpectation P.weight (fun ω ↦ ∑ x ∈ S, (isolate E (configuration S J ω) x : ℝ)) := by
      congr 1
      funext ω
      exact (PositionalCountCumulant.onGround_count S _
        (PositionalDeletionSupport.onGround_mono S
          (PositionalGroundSupport.onGround_configuration S J ω) (isolate_le E (configuration S J ω)))).symm
    _ = ∑ x ∈ S, finiteExpectation P.weight (fun ω ↦ (isolate E (configuration S J ω) x : ℝ)) :=
      finiteExpectation_sum _ _ _
    _ = _ := sum_congr rfl (fun x _hx ↦ (hmean x).symm)

end PaperP1.ErasedCountReference
