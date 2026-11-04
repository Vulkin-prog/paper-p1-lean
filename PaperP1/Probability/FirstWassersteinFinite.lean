module

public import PaperP1.Probability.FirstWassersteinTests

/-! # Finite first Wasserstein laws and the optimal ordered coupling

For two ordered natural observations of the same finite sample, the transport
infimum equals their exact mean difference. The proof includes a lower bound
for every transport plan, so the given coupling is proved optimal.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstWassersteinFinite

open MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.FirstWasserstein

variable {Ω : Type*} [Fintype Ω]

theorem mean_lower_bound (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    |finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) -
      finiteExpectation P.weight (fun ω ↦ (W ω : ℝ))| ≤
      distance (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ⟨finitePlan P Z W⟩ := by
  have hZ := FiniteObservationLaw.integrable P Z (fun k ↦ (k : ℝ))
  have hW := FiniteObservationLaw.integrable P W (fun k ↦ (k : ℝ))
  have hh := FirstWassersteinTests.test_distance_bound
    (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ⟨finitePlan P Z W⟩
    (fun k ↦ (k : ℝ)) ((AtomicTests.integrable_iff_summable _ _).mp hZ)
    ((AtomicTests.integrable_iff_summable _ _).mp hW) (fun _ _ ↦ le_rfl)
  rw [AtomicTests.expectation_eq_integral _ _ hZ, AtomicTests.expectation_eq_integral _ _ hW,
    FiniteObservationLaw.integral_eq, FiniteObservationLaw.integral_eq] at hh
  exact hh

theorem ordered_distance_eq (P : FiniteProbability Ω) (Z W : Ω → ℕ) (hZW : ∀ ω, W ω ≤ Z ω) :
    distance (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ⟨finitePlan P Z W⟩ =
      finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) -
        finiteExpectation P.weight (fun ω ↦ (W ω : ℝ)) := by
  have hreal (ω : Ω) : (W ω : ℝ) ≤ (Z ω : ℝ) := by exact_mod_cast hZW ω
  apply le_antisymm
  · apply (finite_coupling_bound P Z W).trans_eq
    rw [← finiteExpectation_sub]
    congr 1
    funext ω
    exact abs_of_nonneg (sub_nonneg.mpr (hreal ω))
  · have hh := mean_lower_bound P Z W
    rwa [abs_of_nonneg (sub_nonneg.mpr (finiteExpectation_mono P hreal))] at hh

end PaperP1.FirstWassersteinFinite
