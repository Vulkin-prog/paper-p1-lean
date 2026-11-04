module

public import PaperP1.Probability.FiniteOnceAllCoupling
public import PaperP1.Model.OnceErasedCount
public import PaperP1.Model.AllPairOriginalLaws
public import PaperP1.Model.ActiveEdgeBonferroni

/-! # The original once-erased and isolated laws share the literal sample coupling

The positive two-edge moment controls the activation correction, total variation
and first Wasserstein distance with constants one half, one half and one.
These are exact finite inequalities, prior to any arithmetic rate estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OnceAllOriginalCoupling

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalCountProjection

def plan (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ)) :
    FirstWasserstein.Plan (PositionalObservationLaw.law G L (oneCount E))
      (PositionalObservationLaw.law G L (fun v ↦ totalCount (isolate E v))) :=
  FirstWasserstein.finitePlan (cylinderProbability (PositionalObservationLaw.cutoff G L))
    (FiniteOnceAllCoupling.onceObservation G (fun x ↦ startIndicator x L) E)
    (FiniteOnceAllCoupling.allObservation G (fun x ↦ startIndicator x L) E)

theorem factorialCost_eq_second (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, e ⊆ G) :
    FiniteOnceAllCoupling.factorialCost
      (cylinderProbability (PositionalObservationLaw.cutoff G L)) G
      (fun x ↦ startIndicator x L) E = ActiveEdgeBonferroni.factorialSecond E L := by
  have hcut : ∀ e ∈ E, ∀ x ∈ e, x + L ≤ PositionalObservationLaw.cutoff G L := fun e he x hx ↦
    le_sup (f := fun x ↦ x + L) (hE e he hx)
  rw [ActiveEdgeBonferroni.factorialSecond_eq_finite E hcut]
  unfold FiniteOnceAllCoupling.factorialCost
  congr 1
  funext ω
  rw [FiniteDeletedIntensity.active_count_eq_value G _ E hE ω]

theorem factorialSecond_eq_joint {M L : ℕ} (E : Finset (Finset ℕ))
    (hcut : ∀ e ∈ E, ∀ x ∈ e, x + L ≤ M) :
    ActiveEdgeBonferroni.factorialSecond E L =
      ∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2) := by
  rw [← ActiveFamilySecondMoment.infinite_mean_eq E hcut]
  unfold ActiveEdgeBonferroni.factorialSecond
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ ↦ by ring)

theorem finite_bounds (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    AtomicProbability.totalVariation (PositionalObservationLaw.law G L (oneCount E))
      (PositionalObservationLaw.law G L (fun v ↦ totalCount (isolate E v))) ≤
        ActiveEdgeBonferroni.factorialSecond E L / 2 ∧
    FirstWasserstein.distance (PositionalObservationLaw.law G L (oneCount E))
      (PositionalObservationLaw.law G L (fun v ↦ totalCount (isolate E v))) ⟨plan G L E⟩ ≤
        ActiveEdgeBonferroni.factorialSecond E L := by
  have ht := FiniteOnceAllCoupling.totalVariation_bound
    (cylinderProbability (PositionalObservationLaw.cutoff G L)) G
    (fun x ↦ startIndicator x L) E (fun e he ↦ (hE e he).2)
  have hw := FiniteOnceAllCoupling.wasserstein_bound
    (cylinderProbability (PositionalObservationLaw.cutoff G L)) G
    (fun x ↦ startIndicator x L) E (fun e he ↦ (hE e he).2)
  rw [factorialCost_eq_second G L E (fun e he ↦ (hE e he).1)] at ht hw
  exact ⟨ht, hw⟩

def goodPlan (H : ℝ) (N L : ℕ) :
    FirstWasserstein.Plan (OnceErasedCount.law H N L) (AllPairOriginalLaws.goodLaw H N L) := by
  rw [OnceErasedCount.law_eq_observation]
  exact plan (dyadicBlock N) L (GoodEdgeCompression.goodEdges H N L)

def totalVariation (H : ℝ) (N L : ℕ) : ℝ :=
  AtomicProbability.totalVariation (OnceErasedCount.law H N L) (AllPairOriginalLaws.goodLaw H N L)

def wasserstein (H : ℝ) (N L : ℕ) : ℝ :=
  FirstWasserstein.distance (OnceErasedCount.law H N L) (AllPairOriginalLaws.goodLaw H N L)
    ⟨goodPlan H N L⟩

def second (H : ℝ) (N L : ℕ) : ℝ :=
  ActiveEdgeBonferroni.factorialSecond (GoodEdgeCompression.goodEdges H N L) L

def correction (H : ℝ) (N L : ℕ) : ℝ :=
  RetainedReferenceTheorem.beta H N L -
    ActiveEdgeObservables.probability (GoodEdgeCompression.goodEdges H N L) L

theorem totalVariation_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ totalVariation H N L :=
  AtomicProbability.totalVariation_nonneg _ _

theorem wasserstein_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ wasserstein H N L :=
  FirstWasserstein.distance_nonneg _ _ _

theorem good_bounds {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    0 ≤ correction H N L ∧ correction H N L ≤ second H N L / 2 ∧
      totalVariation H N L ≤ second H N L / 2 ∧ wasserstein H N L ≤ second H N L := by
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  have hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2 := fun e he ↦
    ⟨(RetainedGoodEdges.good_pair_regular hN e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he⟩
  have hcut : ∀ e ∈ E, ∀ x ∈ e, x + L ≤ PositionalObservationLaw.cutoff G L := fun e he x hx ↦
    le_sup (f := fun x ↦ x + L) ((hE e he).1 hx)
  have hb := ActiveEdgeBonferroni.union_correction E hcut
  have ht := finite_bounds G L E hE
  refine ⟨hb.1, hb.2, ?_, ?_⟩
  · unfold totalVariation
    rw [OnceErasedCount.law_eq_observation]
    exact ht.1
  · unfold wasserstein FirstWasserstein.distance
    rw [OnceErasedCount.law_eq_observation]
    exact ht.2

theorem second_eq_joint {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    second H N L = ∑ p ∈ ActiveFamilySecondMoment.ordered (GoodEdgeCompression.goodEdges H N L),
      infiniteJointMoment L (p.1 ∪ p.2) := by
  apply factorialSecond_eq_joint (M := PositionalObservationLaw.cutoff (dyadicBlock N) L)
  intro e he x hx
  exact le_sup (f := fun x ↦ x + L)
    (RegularStarts.regularStarts_subset N L (RetainedGoodEdges.good_pair_regular hN e he hx))

end PaperP1.OnceAllOriginalCoupling
