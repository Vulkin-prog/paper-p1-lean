module

public import PaperP1.Probability.FiniteCoupling
public import PaperP1.Model.RegularStarts

/-! # Actual infinite count moments and finite cylinder observations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CountObservables

open MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.Model
open PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
open PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations
open RegularStarts Finset

local instance countObservablesMeasurableF2 : MeasurableSpace F₂ := ⊤

def countMoment (G : Finset ℕ) (L j : ℕ) : ℝ :=
  ∫ ω, (infiniteStartCount G L ω : ℝ) ^ j ∂infiniteRademacherMeasure

def restrictedCountLaw (N L : ℕ) (G : Finset ℕ) : SignedLaw ℝ :=
  countLaw G (cylinderProbability (dyadicCutoff N L)).weight (fun x ↦ startIndicator x L)

def countDisagreement (G H : Finset ℕ) (L : ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | infiniteStartCount G L ω ≠ infiniteStartCount H L ω}

theorem dyadic_subset_cutoff {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    ∀ x ∈ G, x + L ≤ dyadicCutoff N L := by
  intro x hx
  have hxblock := mem_Ico.mp (hG hx)
  unfold dyadicCutoff
  omega

theorem countMoment_eq_finite {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (j : ℕ) :
    countMoment G L j = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) ^ j) := by
  calc
    _ = ∫ ω, (indicatorCount G (fun x ↦ startIndicator x L)
        (restrictToFinite (dyadicCutoff N L) ω) : ℝ) ^ j ∂infiniteRademacherMeasure := by
      unfold countMoment
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg (fun n : ℕ ↦ (n : ℝ) ^ j)
        (infiniteStartCount_restrict G L _ (dyadic_subset_cutoff hG) ω).symm
    _ = _ := infiniteCylinder_integral (dyadicCutoff N L)
      (fun σ ↦ (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) ^ j)

theorem count_observable_integral_eq_finite {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (f : ℕ → ℝ) :
    (∫ ω, f (infiniteStartCount G L ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
        (fun σ ↦ f (indicatorCount G (fun x ↦ startIndicator x L) σ)) := by
  calc
    _ = ∫ ω, f (indicatorCount G (fun x ↦ startIndicator x L)
        (restrictToFinite (dyadicCutoff N L) ω)) ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f
        (infiniteStartCount_restrict G L _ (dyadic_subset_cutoff hG) ω).symm
    _ = _ := infiniteCylinder_integral (dyadicCutoff N L)
      (fun σ ↦ f (indicatorCount G (fun x ↦ startIndicator x L) σ))

theorem countMoment_one {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    countMoment G L 1 = ∑ x ∈ G, infiniteMarginal x L := by
  rw [countMoment_eq_finite hG]
  simp_rw [pow_one]
  rw [mean_indicatorCount]
  apply sum_congr rfl
  intro x hx
  exact (infiniteMarginal_eq_finite (dyadic_subset_cutoff hG x hx)).symm

theorem restrictedCountLaw_isProbability (N L : ℕ) (G : Finset ℕ) :
    IsProbability (restrictedCountLaw N L G) := countLaw_isProbability _ _ _

theorem restrictedCountLaw_coeff {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (k : ℕ) :
    (restrictedCountLaw N L G).coeff k =
      infiniteRademacherMeasure.real {ω | infiniteStartCount G L ω = k} := by
  classical
  unfold restrictedCountLaw
  rw [← finiteCylinder_weights_eq, finiteMeasure_countLaw_coeff,
    ← map_infiniteRademacherMeasure_restrictToFinite (dyadicCutoff N L),
    map_measureReal_apply (measurable_restrictToFinite _) MeasurableSet.of_discrete]
  congr 1
  ext ω
  change indicatorCount G (fun x ↦ startIndicator x L)
    (restrictToFinite (dyadicCutoff N L) ω) = k ↔ _
  rw [infiniteStartCount_restrict G L _ (dyadic_subset_cutoff hG)]
  rfl

theorem restrictedCountLaw_realizes {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    lawMeasure (restrictedCountLaw N L G) (restrictedCountLaw_isProbability N L G).1 =
      infiniteRademacherMeasure.map (infiniteStartCount G L) := by
  apply Measure.ext_of_singleton
  intro k
  rw [lawMeasure_singleton, restrictedCountLaw_coeff hG,
    Measure.map_apply (measurable_infiniteStartCount _ _) (MeasurableSet.singleton k)]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem countDisagreement_eq_finite {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hH : H ⊆ dyadicBlock N) :
    countDisagreement G H L = disagreementProbability (cylinderProbability (dyadicCutoff N L))
      (indicatorCount G (fun x ↦ startIndicator x L))
      (indicatorCount H (fun x ↦ startIndicator x L)) := by
  classical
  unfold countDisagreement disagreementProbability
  rw [← finiteCylinder_event,
    ← map_infiniteRademacherMeasure_restrictToFinite (dyadicCutoff N L),
    map_measureReal_apply (measurable_restrictToFinite _) MeasurableSet.of_discrete]
  congr 1
  ext ω
  change _ ↔ indicatorCount G (fun x ↦ startIndicator x L)
    (restrictToFinite (dyadicCutoff N L) ω) ≠
      indicatorCount H (fun x ↦ startIndicator x L) (restrictToFinite (dyadicCutoff N L) ω)
  rw [infiniteStartCount_restrict G L _ (dyadic_subset_cutoff hG),
    infiniteStartCount_restrict H L _ (dyadic_subset_cutoff hH)]
  rfl

theorem countDisagreement_subset_le {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hHG : H ⊆ G) :
    countDisagreement G H L ≤ ∑ x ∈ G \ H, infiniteMarginal x L := by
  rw [countDisagreement_eq_finite hG (hHG.trans hG)]
  have h := disagreement_count_subset_le (cylinderProbability (dyadicCutoff N L)) hHG
    (fun x ↦ startIndicator x L)
  convert h using 1
  apply sum_congr rfl
  intro x hx
  exact infiniteMarginal_eq_finite (dyadic_subset_cutoff hG x (mem_sdiff.mp hx).1)

theorem count_law_subset_coupling {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hHG : H ⊆ G) :
    lawTotalVariation (restrictedCountLaw N L G) (restrictedCountLaw N L H) ≤
      countDisagreement G H L := by
  rw [countDisagreement_eq_finite hG (hHG.trans hG)]
  unfold restrictedCountLaw
  rw [countLaw_eq_observationLaw, countLaw_eq_observationLaw]
  exact lawTotalVariation_coupling _ _ _

/-- The distance is literally half the sum of absolute differences of actual
infinite-model singleton probabilities; both counts have support in [0,N]. -/
theorem count_law_total_variation_eq {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hH : H ⊆ dyadicBlock N) :
    lawTotalVariation (restrictedCountLaw N L G) (restrictedCountLaw N L H) =
      (∑ k ∈ range ((dyadicBlock N).card + 1),
        |infiniteRademacherMeasure.real {ω | infiniteStartCount G L ω = k} -
          infiniteRademacherMeasure.real {ω | infiniteStartCount H L ω = k}|) / 2 := by
  have hsupport : ((restrictedCountLaw N L G - restrictedCountLaw N L H).coeff).support ⊆
      range ((dyadicBlock N).card + 1) := by
    intro k hk
    by_contra hnot
    have hlarge : (dyadicBlock N).card < k := by
      have h := not_lt.mp (mt mem_range.mpr hnot)
      omega
    have hGlarge : G.card < k := (card_le_card hG).trans_lt hlarge
    have hHlarge : H.card < k := (card_le_card hH).trans_lt hlarge
    have hGzero : (restrictedCountLaw N L G).coeff k = 0 :=
      countLaw_coeff_eq_zero_of_card_lt _ _ _ hGlarge
    have hHzero : (restrictedCountLaw N L H).coeff k = 0 :=
      countLaw_coeff_eq_zero_of_card_lt _ _ _ hHlarge
    have hne := Finsupp.mem_support_iff.mp hk
    exact hne (by simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hGzero, hHzero,
      sub_self])
  rw [lawTotalVariation, l1Norm_eq_sum_of_support_subset _ _ hsupport]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    restrictedCountLaw_coeff hG, restrictedCountLaw_coeff hH]

end PaperP1.CountObservables
