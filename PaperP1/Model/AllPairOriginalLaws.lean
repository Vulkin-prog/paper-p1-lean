module

public import PaperP1.Model.AllPairResidualMass
public import PaperP1.Model.AllPairRetainedGeometry
public import PaperP1.Model.FiniteAllPairCost
public import PaperP1.Model.PositionalObservationLaw

/-! # The genuine original all-pair and good-isolated count laws of T19.14 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairOriginalLaws

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalCountProjection PaperP1.AllPairResidualMass

def goodObservation (H : ℝ) (N L : ℕ) (v : Configuration ℕ) : ℕ :=
  totalCount (isolate (GoodEdgeCompression.goodEdges H N L) v)

def allObservation (N L : ℕ) (v : Configuration ℕ) : ℕ :=
  totalCount (isolate (AllPairDependencyGraph.edges (RegularStarts.regularStarts N L) L)
    (PositionalAllPairCost.restrict (RegularStarts.regularStarts N L) v))

def goodLaw (H : ℝ) (N L : ℕ) : ProbabilityMeasure ℕ :=
  PositionalObservationLaw.law (dyadicBlock N) L (goodObservation H N L)

def allLaw (N L : ℕ) : ProbabilityMeasure ℕ :=
  PositionalObservationLaw.law (dyadicBlock N) L (allObservation N L)

def goodCount (H : ℝ) (N L : ℕ) (ω : InfiniteSample) : ℕ :=
  goodObservation H N L (configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω)

def allCount (N L : ℕ) (ω : InfiniteSample) : ℕ :=
  allObservation N L (configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω)

theorem goodLaw_realMass (H : ℝ) (N L k : ℕ) :
    AtomicProbability.realMass (goodLaw H N L) k = infiniteRademacherMeasure.real
      {ω | goodCount H N L ω = k} :=
  PositionalObservationLaw.realMass_law _ _ _ _

theorem allLaw_realMass (N L k : ℕ) :
    AtomicProbability.realMass (allLaw N L) k = infiniteRademacherMeasure.real
      {ω | allCount N L ω = k} :=
  PositionalObservationLaw.realMass_law _ _ _ _

theorem goodLaw_integral (H : ℝ) (N L : ℕ) (g : ℕ → ℝ) :
    (∫ k, g k ∂(goodLaw H N L : Measure ℕ)) =
      ∫ ω, g (goodCount H N L ω) ∂infiniteRademacherMeasure :=
  PositionalObservationLaw.integral_law _ _ _ _

theorem allLaw_integral (N L : ℕ) (g : ℕ → ℝ) :
    (∫ k, g k ∂(allLaw N L : Measure ℕ)) =
      ∫ ω, g (allCount N L ω) ∂infiniteRademacherMeasure :=
  PositionalObservationLaw.integral_law _ _ _ _

theorem goodLaw_coeff (H : ℝ) (N L k : ℕ) :
    AtomicProbability.realMass (goodLaw H N L) k = CompletedLaw.coeff k
      (projection (PositionalDeletedFields.isolatedLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L)) :=
  PositionalObservationLaw.isolated_count_coeff _ _ _ _

theorem original_cost {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    AtomicProbability.totalVariation (goodLaw H N L) (allLaw N L) ≤ tau H N L ∧
      0 ≤ (∫ k, (k : ℝ) ∂(goodLaw H N L : Measure ℕ)) -
        (∫ k, (k : ℝ) ∂(allLaw N L : Measure ℕ)) ∧
      (∫ k, (k : ℝ) ∂(goodLaw H N L : Measure ℕ)) -
        (∫ k, (k : ℝ) ∂(allLaw N L : Measure ℕ)) ≤ 2 * tau H N L := by
  let S := dyadicBlock N
  let G := RegularStarts.regularStarts N L
  let E := GoodEdgeCompression.goodEdges H N L
  let F := AllPairDependencyGraph.edges G L
  let M := PositionalObservationLaw.cutoff S L
  let P := cylinderProbability M
  let J := fun x ↦ startIndicator (M := M) x L
  have hcut (x : ℕ) (hx : x ∈ S) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2 := AllPairDependencyGraph.edge_data G L
  have hc := FiniteAllPairCost.finite_bounds P S G (RegularStarts.regularStarts_subset N L) J E F
    (AllPairDependencyGraph.good_subset hN hL H) hF
  have hbad : (∑ e ∈ F \ E, finiteJointMoment P J e) = badMass H N L := by
    apply sum_congr rfl
    intro e he
    have heG := (hF e (mem_sdiff.mp he).1).1
    exact (infiniteJointMoment_eq_finite M L e (fun x hx ↦ hcut x
      (RegularStarts.regularStarts_subset N L (heG hx)))).symm
  have hlocal : (∑ x ∈ S \ G, exactMarginal P J x) = localMass N L := by
    apply sum_congr rfl
    intro x hx
    rw [← infiniteMarginal_eq_finite (hcut x (mem_sdiff.mp hx).1)]
  rw [hbad, hlocal] at hc
  have hgoodMean : (∫ k, (k : ℝ) ∂(goodLaw H N L : Measure ℕ)) =
      finiteExpectation P.weight (fun ω ↦ (totalCount (isolate E (configuration S J ω)) : ℝ)) :=
    FiniteObservationLaw.integral_eq _ _ _
  have hallMean : (∫ k, (k : ℝ) ∂(allLaw N L : Measure ℕ)) =
      finiteExpectation P.weight (fun ω ↦ (totalCount (isolate F
        (PositionalAllPairCost.restrict G (configuration S J ω))) : ℝ)) :=
    FiniteObservationLaw.integral_eq _ _ _
  refine ⟨hc.1, ?_, ?_⟩
  · rw [hgoodMean, hallMean]
    exact hc.2.1
  · rw [hgoodMean, hallMean]
    apply hc.2.2.trans
    unfold tau
    have hl := localMass_nonneg N L
    linarith only [hl]

end PaperP1.AllPairOriginalLaws
