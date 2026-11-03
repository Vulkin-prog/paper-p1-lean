module

public import PaperP1.Model.RetainedModifiedLaw
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Probability.AtomicProbabilityMetric

/-! # Actual count-law coupling across arbitrary finite grounds and restoration of deleted starts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalCountLawCoupling

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer
  PaperP1.RetainedModifiedLaw PaperP1.CountObservables

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_law (M L : ℕ) (G : Finset ℕ) (hcut : ∀ x ∈ G, x + L ≤ M) :
    FiniteObservationLaw.law (cylinderProbability M) (indicatorCount G (fun x ↦ startIndicator x L)) =
      originalLaw G L := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_measureReal_singleton
  intro k
  change AtomicProbability.realMass (FiniteObservationLaw.law (cylinderProbability M)
    (indicatorCount G (fun x ↦ startIndicator x L))) k = AtomicProbability.realMass (originalLaw G L) k
  rw [FiniteObservationLaw.realMass_eq, realMass_originalLaw,
    ← infiniteCylinder_event M (fun σ ↦ indicatorCount G (fun x ↦ startIndicator x L) σ = k)]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, infiniteStartCount_restrict G L M hcut]

theorem coupling (L : ℕ) (G H : Finset ℕ) :
    AtomicProbability.totalVariation (originalLaw G L) (originalLaw H L) ≤ countDisagreement G H L := by
  let M := MaximumDirectActive.cutoff (G ∪ H) L
  have hcutG : ∀ x ∈ G, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) (mem_union_left H hx)
  have hcutH : ∀ x ∈ H, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) (mem_union_right G hx)
  have hcouple := FiniteObservationLaw.coupling (cylinderProbability M)
    (indicatorCount G (fun x ↦ startIndicator x L)) (indicatorCount H (fun x ↦ startIndicator x L))
  rw [finite_law M L G hcutG, finite_law M L H hcutH] at hcouple
  apply hcouple.trans_eq
  rw [disagreementProbability,
    ← infiniteCylinder_event M (fun σ ↦ indicatorCount G (fun x ↦ startIndicator x L) σ ≠
      indicatorCount H (fun x ↦ startIndicator x L) σ)]
  unfold countDisagreement
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, infiniteStartCount_restrict G L M hcutG, infiniteStartCount_restrict H L M hcutH]

theorem restore_modified (H : ℝ) (N L : ℕ) :
    AtomicProbability.totalVariation (originalLaw (dyadicBlock N) L)
      (law H N L (RegularStarts.regularStarts N L)) ≤
      countDisagreement (dyadicBlock N) (RegularStarts.regularStarts N L) L +
        RetainedCountCylinder.badProbability H N L (RegularStarts.regularStarts N L) :=
  (AtomicProbabilityMetric.triangle _ (originalLaw (RegularStarts.regularStarts N L) L) _).trans
    (add_le_add (coupling L _ _) (RetainedModifiedLaw.coupling H N L _))

end PaperP1.OriginalCountLawCoupling
