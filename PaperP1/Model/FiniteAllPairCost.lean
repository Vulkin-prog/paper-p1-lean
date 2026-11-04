module

public import PaperP1.Model.FiniteDeletedIntensity
public import PaperP1.Probability.PositionalAllPairCost
public import PaperP1.Probability.FiniteObservationLaw

/-! # Actual finite laws and means of the all-pair deletion coupling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteAllPairCost

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.PositionalFiniteLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalCountProjection PaperP1.PositionalAllPairCost

variable {ι Ω : Type*} [Fintype Ω] [DecidableEq ι]

omit [Fintype Ω] in
theorem outside_configuration (H G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    outside G (configuration H J ω) = configuration (H \ G) J ω := by
  classical
  ext x
  by_cases hx : x ∈ H \ G
  · rw [outside, Finsupp.filter_apply, ite_eq_left (mem_sdiff.mp hx).2,
      PositionalGrid.configuration_apply_mem H J ω ⟨x, (mem_sdiff.mp hx).1⟩,
      PositionalGrid.configuration_apply_mem (H \ G) J ω ⟨x, hx⟩]
  · rw [PositionalGroundSupport.onGround_configuration (H \ G) J ω x hx]
    rw [outside, Finsupp.filter_apply]
    by_cases hxG : x ∈ G
    · rw [ite_eq_right (not_not.mpr hxG)]
    · rw [ite_eq_left hxG]
      exact PositionalGroundSupport.onGround_configuration H J ω x
        (fun hxH ↦ hx (mem_sdiff.mpr ⟨hxH, hxG⟩))

theorem expected_outside (P : FiniteProbability Ω) (H G : Finset ι) (J : ι → Ω → Bool) :
    finiteExpectation P.weight (fun ω ↦ (totalCount (outside G (configuration H J ω)) : ℝ)) =
      ∑ x ∈ H \ G, exactMarginal P J x := by
  simp only [outside_configuration, totalCount_configuration]
  exact mean_indicatorCount P (H \ G) J

omit [DecidableEq ι] in
theorem expected_active (P : FiniteProbability Ω) (H : Finset ι) (J : ι → Ω → Bool)
    (D : Finset (Finset ι)) (hD : ∀ e ∈ D, e ⊆ H) :
    finiteExpectation P.weight (fun ω ↦ ((activeEdges D (configuration H J ω)).card : ℝ)) =
      ∑ e ∈ D, finiteJointMoment P J e := by
  simp_rw [FiniteDeletedIntensity.active_count_eq_value H J D hD]
  exact ActivePairCount.mean_eq P D J

theorem finite_bounds (P : FiniteProbability Ω) (H G : Finset ι) (hGH : G ⊆ H)
    (J : ι → Ω → Bool) (E F : Finset (Finset ι)) (hEF : E ⊆ F)
    (hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2) :
    let Z := fun ω ↦ totalCount (isolate E (configuration H J ω))
    let W := fun ω ↦ totalCount (isolate F (PositionalAllPairCost.restrict G (configuration H J ω)))
    let b := ∑ e ∈ F \ E, finiteJointMoment P J e
    let l := ∑ x ∈ H \ G, exactMarginal P J x
    AtomicProbability.totalVariation (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ≤ b + l ∧
      0 ≤ finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) - finiteExpectation P.weight (fun ω ↦ (W ω : ℝ)) ∧
      finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) - finiteExpectation P.weight (fun ω ↦ (W ω : ℝ)) ≤ 2 * b + l := by
  let Z := fun ω ↦ totalCount (isolate E (configuration H J ω))
  let W := fun ω ↦ totalCount (isolate F (PositionalAllPairCost.restrict G (configuration H J ω)))
  have hD : ∀ e ∈ F \ E, e ⊆ H := fun e he ↦ ((hF e (mem_sdiff.mp he).1).1).trans hGH
  have hcost (ω : Ω) := full_cost G E F (configuration H J ω)
    (PositionalDeletedFields.configuration_binary H J ω) hEF hF
  have hlow : finiteExpectation P.weight (fun ω ↦ (W ω : ℝ)) ≤
      finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ)) :=
    finiteExpectation_mono P (fun ω ↦ by exact_mod_cast (hcost ω).1)
  have hmean : finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ) - (W ω : ℝ)) ≤
      2 * (∑ e ∈ F \ E, finiteJointMoment P J e) + ∑ x ∈ H \ G, exactMarginal P J x := by
    calc
      _ ≤ finiteExpectation P.weight (fun ω ↦
          2 * ((activeEdges (F \ E) (configuration H J ω)).card : ℝ) +
            (totalCount (outside G (configuration H J ω)) : ℝ)) := by
        apply finiteExpectation_mono P
        intro ω
        have hh : Z ω ≤ W ω + 2 * (activeEdges (F \ E) (configuration H J ω)).card +
            totalCount (outside G (configuration H J ω)) := by
          dsimp only [Z, W]
          have h := hcost ω
          omega
        have hr : (Z ω : ℝ) ≤ W ω + 2 * ((activeEdges (F \ E) (configuration H J ω)).card : ℝ) +
            (totalCount (outside G (configuration H J ω)) : ℝ) := by exact_mod_cast hh
        linarith only [hr]
      _ = _ := by rw [finiteExpectation_add, finiteExpectation_const_mul,
        expected_active P H J (F \ E) hD, expected_outside]
  have htv : AtomicProbability.totalVariation (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ≤
      (∑ e ∈ F \ E, finiteJointMoment P J e) + ∑ x ∈ H \ G, exactMarginal P J x := by
    apply (FiniteObservationLaw.coupling P Z W).trans
    unfold disagreementProbability
    calc
      _ ≤ finiteExpectation P.weight (fun ω ↦ ((activeEdges (F \ E) (configuration H J ω)).card : ℝ) +
          (totalCount (outside G (configuration H J ω)) : ℝ)) := by
        apply finiteExpectation_mono P
        intro ω
        have hh := disagreement_cost G E F (configuration H J ω)
          (PositionalDeletedFields.configuration_binary H J ω) hEF hF
        exact_mod_cast hh
      _ = _ := by rw [finiteExpectation_add, expected_active P H J (F \ E) hD, expected_outside]
  rw [finiteExpectation_sub] at hmean
  exact ⟨htv, sub_nonneg.mpr hlow, hmean⟩

end PaperP1.FiniteAllPairCost
