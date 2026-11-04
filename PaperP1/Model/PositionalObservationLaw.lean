module

public import PaperP1.Model.PositionalDeletedFields
public import PaperP1.Probability.FiniteObservationLaw

/-! # Genuine scalar laws of arbitrary observations of the original field

All finite-cutoff laws are identified with the original infinite prime-sign
event probabilities and Bochner expectations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalObservationLaw

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations
  PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw

def cutoff (G : Finset ℕ) (L : ℕ) : ℕ := G.sup (fun x ↦ x + L)

def law (G : Finset ℕ) (L : ℕ) (f : Configuration ℕ → ℕ) : ProbabilityMeasure ℕ :=
  FiniteObservationLaw.law (cylinderProbability (cutoff G L))
    (fun σ ↦ f (configuration G (fun x ↦ startIndicator x L) σ))

theorem realMass_law (G : Finset ℕ) (L : ℕ) (f : Configuration ℕ → ℕ) (k : ℕ) :
    AtomicProbability.realMass (law G L f) k = infiniteRademacherMeasure.real
      {ω | f (configuration G (fun x ↦ infiniteStartIndicator x L) ω) = k} := by
  rw [law, FiniteObservationLaw.realMass_eq,
    ← infiniteCylinder_event (cutoff G L) (fun σ ↦ f (configuration G (fun x ↦ startIndicator x L) σ) = k)]
  congr 1
  ext ω
  change f (configuration G (fun x ↦ startIndicator x L) (restrictToFinite (cutoff G L) ω)) = k ↔
    f (configuration G (fun x ↦ infiniteStartIndicator x L) ω) = k
  rw [PositionalStoppedLaw.configuration_restrict G L (cutoff G L)
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) ω]

theorem integral_law (G : Finset ℕ) (L : ℕ) (f : Configuration ℕ → ℕ) (g : ℕ → ℝ) :
    (∫ k, g k ∂(law G L f : Measure ℕ)) =
      ∫ ω, g (f (configuration G (fun x ↦ infiniteStartIndicator x L) ω)) ∂infiniteRademacherMeasure := by
  rw [law, FiniteObservationLaw.integral_eq, ← infiniteCylinder_integral (cutoff G L)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ congrArg (fun v ↦ g (f v))
    (PositionalStoppedLaw.configuration_restrict G L (cutoff G L)
      (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) ω))

theorem push_count_coeff (G : Finset ℕ) (L : ℕ) (f : Configuration ℕ → Configuration ℕ) (k : ℕ) :
    AtomicProbability.realMass (law G L (fun v ↦ PositionalCountProjection.totalCount (f v))) k =
      CompletedLaw.coeff k (PositionalCountProjection.projection
        (PositionalDeterministicMap.push f (PositionalDeletedFields.original G L))) := by
  classical
  rw [law, FiniteObservationLaw.realMass_eq, PositionalDeterministicMap.push,
    PositionalDeletedFields.original, PositionalStoppedLaw.actualLaw,
    PositionalDeletedFields.action_finite_law, map_sum, map_sum]
  simp only [map_smul, PositionalCountProjection.projection_atom, CompletedLaw.coeff_ofFinite,
    Probability.atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
  rfl

theorem isolated_count_coeff (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ)) (k : ℕ) :
    AtomicProbability.realMass (law G L (fun v ↦ PositionalCountProjection.totalCount
      (PositionalPairDeletion.isolate E v))) k =
      CompletedLaw.coeff k (PositionalCountProjection.projection (PositionalDeletedFields.isolatedLaw E G L)) :=
  push_count_coeff G L (PositionalPairDeletion.isolate E) k

end PaperP1.PositionalObservationLaw
