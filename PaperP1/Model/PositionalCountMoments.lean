module

public import PaperP1.Probability.PositionalCountTests
public import PaperP1.Model.PositionalStoppedLaw
public import PaperP1.Model.OriginalLawPolynomialMoments

/-! # Exact polynomial count tests for the original positional field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountMoments

open Finset PaperP1.Model PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection

theorem finiteMap_law {Ω ι : Type*} [Fintype Ω]
    (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    finiteMap (PositionalFiniteLaw.law G w J) = Probability.countLaw G w J := by
  classical
  unfold PositionalFiniteLaw.law Probability.countLaw
  simp_rw [FiniteConvolutionAlgebra.scalar_mul_atom, Probability.scalar_mul_atom]
  rw [map_sum]
  apply sum_congr rfl
  intro ω _
  rw [← finiteLinear_eq, finiteLinear_single, totalCount_configuration]
  rfl

theorem projection_actual_coeff (G : Finset ℕ) (L k : ℕ) :
    CompletedLaw.coeff k (projection (CompletedPositionalLaw.ofFinite
      (PositionalStoppedLaw.actualLaw G L))) =
      AtomicProbability.realMass (RetainedModifiedLaw.originalLaw G L) k := by
  let M := G.sup fun x ↦ x + L
  have hcut : ∀ x ∈ G, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  rw [projection_ofFinite, CompletedLaw.coeff_ofFinite,
    PositionalStoppedLaw.actualLaw, finiteMap_law]
  rw [← OriginalCountLawCoupling.finite_law M L G hcut,
    FiniteObservationLaw.realMass_eq_coeff, Probability.countLaw_eq_observationLaw]

theorem weighted_moment_bound (G : Finset ℕ) (L r : ℕ) :
    Summable (fun v : Configuration ℕ ↦ (PositionalStoppedLaw.actualLaw G L).coeff v *
      (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v : Configuration ℕ, (PositionalStoppedLaw.actualLaw G L).coeff v *
        (1 + (totalCount v : ℝ)) ^ r) ≤
          (2 : ℝ) ^ r * (1 + CountObservables.countMoment G L r) := by
  let A := CompletedPositionalLaw.ofFinite (PositionalStoppedLaw.actualLaw G L)
  have ha (v : Configuration ℕ) : 0 ≤ CompletedPositionalLaw.coeff v A := by
    simpa only [A, CompletedPositionalLaw.coeff_ofFinite] using
      PositionalStoppedLaw.actualLaw_nonneg G L v
  have hscalar := OriginalLawPolynomialMoments.weighted_moment_bound G L r
  have hs : Summable (fun k : ℕ ↦ CompletedLaw.coeff k (projection A) * (1 + (k : ℝ)) ^ r) := by
    simpa only [A, projection_actual_coeff] using hscalar.1
  have hv := PositionalCountTests.summable_test A ha (fun k ↦ (1 + (k : ℝ)) ^ r)
    (fun k ↦ by positivity) hs
  have he := PositionalCountTests.test_eq A ha (fun k ↦ (1 + (k : ℝ)) ^ r)
    (fun k ↦ by positivity) hs
  simp only [A, CompletedPositionalLaw.coeff_ofFinite, projection_actual_coeff] at hv he
  exact ⟨hv, he.trans_le hscalar.2⟩

end PaperP1.PositionalCountMoments
