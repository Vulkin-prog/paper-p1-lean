module

public import PaperP1.Model.ConditionalRunProbability

/-! # The original conditional count expectation is the sum of exact conditional start masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalCountMean

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Algebra PaperP1.Probability PaperP1.ConditionalRunRank PaperP1.ConditionalRunProbability
  PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance conditionalCountDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def conditionalCountExpectation {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) (G : Finset ℕ) (L : ℕ) : ℝ :=
  (∫ ω, if infiniteOldEvent R a ω then (infiniteStartCount G L ω : ℝ) else 0 ∂infiniteRademacherMeasure) /
    infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω}

theorem conditionalCountExpectation_eq_finite {M L : ℕ} {R G : Finset ℕ}
    (hcut : ∀ x ∈ G, x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalCountExpectation R a G L =
      finiteExpectation (cylinderProbability M).weight
        (fun σ ↦ if finiteOldEvent R a σ then (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) else 0) /
          oldObservationMass (oldRows M R) a := by
  have hfun : (fun ω ↦ if infiniteOldEvent R a ω then (infiniteStartCount G L ω : ℝ) else 0) =
      (fun ω ↦ if finiteOldEvent R a (restrictToFinite M ω) then
        (indicatorCount G (fun x ↦ startIndicator x L) (restrictToFinite M ω) : ℝ) else 0) := by
    funext ω
    rw [oldEvent_restrict hR, infiniteStartCount_restrict G L M hcut]
  unfold conditionalCountExpectation
  rw [hfun, infiniteCylinder_integral M (fun σ ↦ if finiteOldEvent R a σ then
    (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) else 0), observation_probability hR]

theorem conditionalCountExpectation_eq_sum {M L : ℕ} {R G : Finset ℕ}
    (hL : 0 < L) (hcut : ∀ x ∈ G, x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalCountExpectation R a G L = ∑ x ∈ G, conditionalStartProbability R a x L := by
  rw [conditionalCountExpectation_eq_finite hcut hR]
  have hfun : (fun σ : SampleSpace M ↦ if finiteOldEvent R a σ then
      (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) else 0) =
      (fun σ ↦ ∑ x ∈ G, if finiteOldEvent R a σ ∧ startIndicator x L σ = true then (1 : ℝ) else 0) := by
    funext σ
    by_cases h : finiteOldEvent R a σ
    · simp only [h, ite_true, true_and, indicatorCount, Nat.cast_sum]
      apply sum_congr rfl
      intro x _
      cases hJ : startIndicator x L σ <;> norm_num [hJ]
    · simp only [h, ite_false, false_and, sum_const_zero]
  rw [hfun, finiteExpectation_sum, sum_div]
  apply sum_congr rfl
  intro x hx
  rw [conditionalStartProbability_eq_affine hL (hcut x hx) hR]
  unfold conditionalAffineMass
  congr 1
  apply congrArg (finiteExpectation (cylinderProbability M).weight)
  funext σ
  simp only [oldRows_event_iff, startIndicator_eq_true_iff, ← startSystem_eq_startRhs_iff σ hL]

end PaperP1.ConditionalCountMean
