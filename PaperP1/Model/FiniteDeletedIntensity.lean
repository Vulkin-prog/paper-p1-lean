module

public import PaperP1.Model.PositionalDeletedFields
public import PaperP1.Probability.PositionalDeletionIntensity
public import PaperP1.Probability.PositionalFiniteExpectations
public import PaperP1.Probability.PositionalCompoundPoisson
public import PaperP1.Model.ActiveFamilySecondMoment

/-! # Finite intensity comparison for both actual deletion kernels

The error is the original marginal bias plus the positive second factorial
moment of the active-edge count. No independence is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteDeletedIntensity

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalDeletionKernels PaperP1.PositionalDeletionIntensity
  PaperP1.PositionalFactorialCovariance

variable {ι Ω : Type*} [Fintype Ω]

local instance finiteIntensityDecidable (P : Prop) : Decidable P := Classical.propDecidable P

omit [Fintype Ω] in
theorem configuration_active (G e : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (he : e ⊆ G) :
    (∀ x ∈ e, 0 < configuration G J ω x) ↔ ∀ x ∈ e, J x ω = true := by
  have hx (x : ι) (hxe : x ∈ e) :
      (0 < configuration G J ω x) ↔ J x ω = true := by
    rw [PositionalGrid.configuration_apply_mem G J ω ⟨x, he hxe⟩]
    cases J x ω <;> decide
  exact ⟨fun h x hxe ↦ (hx x hxe).mp (h x hxe), fun h x hxe ↦ (hx x hxe).mpr (h x hxe)⟩

omit [Fintype Ω] in
theorem incident_configuration (G : Finset ι) (J : ι → Ω → Bool) (E : Finset (Finset ι))
    (hE : ∀ e ∈ E, e ⊆ G) (ω : Ω) (x : ι) :
    incident E (configuration G J ω) x =
      ∑ e ∈ E, if x ∈ e then ∏ y ∈ e, (indicatorValue (J y ω) : ℝ) else 0 := by
  rw [incident, activeEdges, sum_filter]
  apply sum_congr rfl
  intro e he
  rw [indicator_product_eq_indicator]
  have hactive := configuration_active G e J ω (hE e he)
  by_cases ha : ∀ y ∈ e, J y ω = true
  · rw [ite_eq_left (hactive.mpr ha), ite_eq_left ha]
  · rw [ite_eq_right (fun h ↦ ha (hactive.mp h)), ite_eq_right ha]
    split_ifs <;> rfl

omit [Fintype Ω] in
theorem active_count_eq_value (G : Finset ι) (J : ι → Ω → Bool) (E : Finset (Finset ι))
    (hE : ∀ e ∈ E, e ⊆ G) (ω : Ω) :
    ((activeEdges E (configuration G J ω)).card : ℝ) = ActivePairCount.value E J ω := by
  classical
  rw [ActivePairCount.value_eq_card]
  congr 1
  apply congrArg Finset.card
  ext e
  simp only [activeEdges, mem_filter]
  exact and_congr_right (fun he ↦ configuration_active G e J ω (hE e he))

theorem finite_factorial_eq (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e ⊆ G) :
    finiteExpectation P.weight (fun ω ↦ ((activeEdges E (configuration G J ω)).card : ℝ) *
      (((activeEdges E (configuration G J ω)).card : ℝ) - 1)) =
        ∑ p ∈ ActiveFamilySecondMoment.ordered E, finiteJointMoment P J (p.1 ∪ p.2) := by
  classical
  have hpoint (ω : Ω) : ((activeEdges E (configuration G J ω)).card : ℝ) *
      (((activeEdges E (configuration G J ω)).card : ℝ) - 1) =
      ∑ p ∈ ActiveFamilySecondMoment.ordered E, ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ) := by
    rw [active_count_eq_value G J E hE ω]
    have hh := ActiveFamilySecondMoment.factorial_value E J ω
    nlinarith only [hh]
  simp_rw [hpoint]
  exact finiteExpectation_sum _ _ _

theorem expected_incident (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e ⊆ G) (x : ι) :
    finiteExpectation P.weight (fun ω ↦ incident E (configuration G J ω) x) =
      PositionalCompoundPoisson.incidence E (finiteJointMoment P J) x := by
  simp_rw [incident_configuration G J E hE]
  rw [finiteExpectation_sum]
  unfold PositionalCompoundPoisson.incidence
  apply sum_congr rfl
  intro e _he
  by_cases hx : x ∈ e
  · simp only [ite_eq_left hx]
    rfl
  · simp only [ite_eq_right hx, finiteExpectation, mul_zero, sum_const_zero]

theorem mean_original (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool) (x : ι) :
    mean (ofFinite (law G P.weight J)) x =
      finiteExpectation P.weight (fun ω ↦ (configuration G J ω x : ℝ)) :=
  (PositionalFiniteExpectations.hasSum_law G P.weight J (fun v ↦ (v x : ℝ))).tsum_eq

theorem coordinate_marginal (P : FiniteProbability Ω) (G : Finset ι)
    (J : ι → Ω → Bool) (x : ι) (hx : x ∈ G) :
    finiteExpectation P.weight (fun ω ↦ (configuration G J ω x : ℝ)) = exactMarginal P J x := by
  unfold exactMarginal
  congr 1
  funext ω
  rw [PositionalGrid.configuration_apply_mem G J ω ⟨x, hx⟩]
  cases J x ω <;> norm_num [indicatorValue]

theorem mean_once (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (x : ι) :
    mean (once E (ofFinite (law G P.weight J))) x =
      finiteExpectation P.weight (fun ω ↦
        (configuration G J ω x : ℝ) - removedOnce E (configuration G J ω) x) := by
  rw [once, PositionalDeletedFields.action_finite_law]
  have hs := PositionalFiniteExpectations.hasSum_mixture P.weight
    (fun ω ↦ onceKernel E (configuration G J ω)) (fun v ↦ (v x : ℝ))
    (fun ω ↦ (configuration G J ω x : ℝ) - removedOnce E (configuration G J ω) x) (fun ω ↦ by
      have hh := (onceKernel_test_summable E (configuration G J ω) (fun v ↦ (v x : ℝ))).hasSum
      rw [show (∑' v, coeff v (onceKernel E (configuration G J ω)) * (v x : ℝ)) =
        mean (onceKernel E (configuration G J ω)) x from rfl, onceKernel_mean] at hh
      exact hh)
  exact hs.tsum_eq

theorem mean_isolated (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (x : ι) :
    mean (isolated E (ofFinite (law G P.weight J))) x =
      finiteExpectation P.weight (fun ω ↦
        (configuration G J ω x : ℝ) - removedAll E (configuration G J ω) x) := by
  rw [isolated, PositionalDeterministicMap.push, PositionalDeletedFields.action_finite_law]
  have hs := PositionalFiniteExpectations.hasSum_mixture P.weight
    (fun ω ↦ ofFinite (FiniteConvolutionAlgebra.atom (isolate E (configuration G J ω))))
    (fun v ↦ (v x : ℝ)) (fun ω ↦ (configuration G J ω x : ℝ) - removedAll E (configuration G J ω) x)
    (fun ω ↦ by
      have hh := PositionalDeterministicMap.hasSum_atom_test
        (isolate E (configuration G J ω)) (fun v ↦ (v x : ℝ))
      rwa [isolate_coordinate] at hh)
  exact hs.tsum_eq

theorem intensity_transfer (P : FiniteProbability Ω) (G : Finset ι)
    (v : Ω → Configuration ι) (E : Finset (Finset ι)) (b : ι → ℝ)
    (r : Ω → ι → ℝ) (F : Ω → ℝ)
    (hr : ∀ ω x, r ω x ≤ incident E (v ω) x)
    (hF : ∀ ω, (∑ x ∈ G, (incident E (v ω) x - r ω x)) ≤ F ω) :
    (∑ x ∈ G, |finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ) - r ω x) -
      (b x - finiteExpectation P.weight (fun ω ↦ incident E (v ω) x))|) ≤
      (∑ x ∈ G, |finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ)) - b x|) +
        finiteExpectation P.weight F := by
  have hpoint (x : ι) :
      |finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ) - r ω x) -
        (b x - finiteExpectation P.weight (fun ω ↦ incident E (v ω) x))| ≤
      |finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ)) - b x| +
        finiteExpectation P.weight (fun ω ↦ incident E (v ω) x - r ω x) := by
    have hnonneg := finiteExpectation_nonneg P (fun ω ↦ sub_nonneg.mpr (hr ω x))
    have he : finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ) - r ω x) -
        (b x - finiteExpectation P.weight (fun ω ↦ incident E (v ω) x)) =
        (finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ)) - b x) +
          finiteExpectation P.weight (fun ω ↦ incident E (v ω) x - r ω x) := by
      rw [finiteExpectation_sub, finiteExpectation_sub]
      ring
    rw [he]
    exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg hnonneg])
  calc
    _ ≤ ∑ x ∈ G, (|finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ)) - b x| +
        finiteExpectation P.weight (fun ω ↦ incident E (v ω) x - r ω x)) := sum_le_sum (fun x _hx ↦ hpoint x)
    _ = (∑ x ∈ G, |finiteExpectation P.weight (fun ω ↦ (v ω x : ℝ)) - b x|) +
        finiteExpectation P.weight (fun ω ↦ ∑ x ∈ G, (incident E (v ω) x - r ω x)) := by
      rw [sum_add_distrib, finiteExpectation_sum]
    _ ≤ _ := add_le_add le_rfl (finiteExpectation_mono P hF)

theorem once_bound (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (b : ι → ℝ) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, |mean (once E (ofFinite (law G P.weight J))) x -
      (b x - PositionalCompoundPoisson.incidence E (finiteJointMoment P J) x)|) ≤
      (∑ x ∈ G, |exactMarginal P J x - b x|) +
        finiteExpectation P.weight (fun ω ↦ ((activeEdges E (configuration G J ω)).card : ℝ) *
          (((activeEdges E (configuration G J ω)).card : ℝ) - 1)) := by
  have hh := intensity_transfer P G (configuration G J) E b
    (fun ω x ↦ removedOnce E (configuration G J ω) x) _
    (fun ω x ↦ (removedOnce_bounds E (configuration G J ω) x).2)
    (fun ω ↦ once_factorial_remainder G E (configuration G J ω) hE)
  simp only [← mean_once, expected_incident P G J E (fun e he ↦ (hE e he).1)] at hh
  apply hh.trans_eq
  congr 1
  apply sum_congr rfl
  intro x hx
  rw [coordinate_marginal P G J x hx]

theorem isolated_bound (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (b : ι → ℝ) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    (∑ x ∈ G, |mean (isolated E (ofFinite (law G P.weight J))) x -
      (b x - PositionalCompoundPoisson.incidence E (finiteJointMoment P J) x)|) ≤
      (∑ x ∈ G, |exactMarginal P J x - b x|) +
        finiteExpectation P.weight (fun ω ↦ ((activeEdges E (configuration G J ω)).card : ℝ) *
          (((activeEdges E (configuration G J ω)).card : ℝ) - 1)) := by
  have hh := intensity_transfer P G (configuration G J) E b
    (fun ω x ↦ removedAll E (configuration G J ω) x) _
    (fun ω x ↦ (removedAll_bounds E (configuration G J ω)
      (PositionalDeletedFields.configuration_binary G J ω) x).2)
    (fun ω ↦ isolated_factorial_remainder G E (configuration G J ω)
      (PositionalDeletedFields.configuration_binary G J ω) hE)
  simp only [← mean_isolated, expected_incident P G J E (fun e he ↦ (hE e he).1)] at hh
  apply hh.trans_eq
  congr 1
  apply sum_congr rfl
  intro x hx
  rw [coordinate_marginal P G J x hx]

end PaperP1.FiniteDeletedIntensity
