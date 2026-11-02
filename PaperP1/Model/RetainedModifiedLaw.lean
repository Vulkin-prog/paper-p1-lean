module

public import PaperP1.Model.RetainedCountCylinder

/-! # Actual original and retained-modified probability laws and their coupling

The error is the literal probability of a nonretained active configuration.
No asymptotic bound on this probability is supplied or claimed here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedModifiedLaw

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Probability
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.MaximumDirectActive
  PaperP1.RetainedActiveCount PaperP1.RetainedCountCylinder

local instance retainedModifiedLawMeasurableF2 : MeasurableSpace F₂ := ⊤

def law (H : ℝ) (N L : ℕ) (G : Finset ℕ) : ProbabilityMeasure ℕ :=
  FiniteObservationLaw.law (cylinderProbability (cutoff G L)) (finiteModified H N L G)

def originalLaw (G : Finset ℕ) (L : ℕ) : ProbabilityMeasure ℕ :=
  FiniteObservationLaw.law (cylinderProbability (cutoff G L)) (indicatorCount G (fun x ↦ startIndicator x L))

theorem realMass_law (H : ℝ) (N L : ℕ) (G : Finset ℕ) (k : ℕ) :
    AtomicProbability.realMass (law H N L G) k =
      infiniteRademacherMeasure.real {ω | modified H N L G ω = k} := by
  rw [law, FiniteObservationLaw.realMass_eq]
  convert (event_probability H N L G (fun n ↦ n = k)).symm using 1
  congr 1
  funext σ
  split_ifs <;> rfl

theorem realMass_originalLaw (G : Finset ℕ) (L k : ℕ) :
    AtomicProbability.realMass (originalLaw G L) k =
      infiniteRademacherMeasure.real {ω | infiniteStartCount G L ω = k} := by
  rw [originalLaw, FiniteObservationLaw.realMass_eq]
  convert (original_event_probability G L (fun n ↦ n = k)).symm using 1
  congr 1
  funext σ
  split_ifs <;> rfl

theorem law_eq_actual_map (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    (law H N L G : Measure ℕ) = infiniteRademacherMeasure.map (modified H N L G) := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  change AtomicProbability.realMass (law H N L G) k = _
  rw [realMass_law, map_measureReal_apply (measurable_modified H N L G) (measurableSet_singleton k)]
  rfl

theorem originalLaw_eq_actual_map (G : Finset ℕ) (L : ℕ) :
    (originalLaw G L : Measure ℕ) = infiniteRademacherMeasure.map (infiniteStartCount G L) := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  change AtomicProbability.realMass (originalLaw G L) k = _
  rw [realMass_originalLaw, map_measureReal_apply (measurable_infiniteStartCount G L) (measurableSet_singleton k)]
  rfl

theorem integrable_law (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : ℕ → ℝ) :
    Integrable f (law H N L G : Measure ℕ) := FiniteObservationLaw.integrable _ _ _

theorem integral_law (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂(law H N L G : Measure ℕ)) =
      ∫ ω, f (modified H N L G ω) ∂infiniteRademacherMeasure := by
  rw [law, FiniteObservationLaw.integral_eq, RetainedCountCylinder.observable_integral]

theorem coupling (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    AtomicProbability.totalVariation (originalLaw G L) (law H N L G) ≤ badProbability H N L G := by
  rw [AtomicProbability.totalVariation_symm (originalLaw G L) (law H N L G)]
  exact (FiniteObservationLaw.coupling (cylinderProbability (cutoff G L))
    (finiteModified H N L G) (indicatorCount G (fun x ↦ startIndicator x L))).trans_eq
      (badProbability_eq_disagreement H N L G).symm

end PaperP1.RetainedModifiedLaw
