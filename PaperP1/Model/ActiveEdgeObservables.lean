module

public import PaperP1.Probability.ActivePairCount
public import PaperP1.Model.CountObservables
public import PaperP1.Model.InfiniteJointMoments

/-! # Actual active-edge counts, their original-model union probability and truncation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveEdgeObservables

open Finset MeasureTheory PaperP1.Algebra PaperP1.Arithmetic PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer

local instance : MeasurableSpace F₂ := ⊤
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def value (F : Finset (Finset ℕ)) (L : ℕ) (ω : InfiniteSample) : ℝ :=
  ActivePairCount.value F (fun x ↦ infiniteStartIndicator x L) ω

def probability (F : Finset (Finset ℕ)) (L : ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | 0 < value F L ω}

theorem positive_iff (F : Finset (Finset ℕ)) (L : ℕ) (ω : InfiniteSample) :
    0 < value F L ω ↔ ∃ e ∈ F, ∀ x ∈ e, infiniteStartIndicator x L ω = true :=
  (ActivePairCount.active_iff_positive F (fun x ↦ infiniteStartIndicator x L) ω).symm

theorem value_restrict {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) (ω : InfiniteSample) :
    ActivePairCount.value F (fun x ↦ startIndicator x L) (restrictToFinite M ω) = value F L ω := by
  apply sum_congr rfl
  intro e he
  apply prod_congr rfl
  intro x hx
  change indicatorValue (startIndicator x L (restrictToFinite M ω)) = indicatorValue (infiniteStartIndicator x L ω)
  rw [startIndicator_restrict_eq ω (hcut e he x hx)]

theorem integral_eq_finite {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) (f : ℝ → ℝ) :
    (∫ ω, f (value F L ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability M).weight
        (fun σ ↦ f (ActivePairCount.value F (fun x ↦ startIndicator x L) σ)) := by
  calc
    _ = ∫ ω, f (ActivePairCount.value F (fun x ↦ startIndicator x L) (restrictToFinite M ω))
        ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f (value_restrict F hcut ω).symm
    _ = _ := infiniteCylinder_integral M (fun σ ↦ f (ActivePairCount.value F (fun x ↦ startIndicator x L) σ))

theorem finite_mean_eq {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    finiteExpectation (cylinderProbability M).weight (ActivePairCount.value F (fun x ↦ startIndicator x L)) =
      ∑ e ∈ F, infiniteJointMoment L e := by
  rw [ActivePairCount.mean_eq]
  apply sum_congr rfl
  intro e he
  exact (infiniteJointMoment_eq_finite M L e (hcut e he)).symm

theorem mean_eq {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    (∫ ω, value F L ω ∂infiniteRademacherMeasure) = ∑ e ∈ F, infiniteJointMoment L e := by
  calc
    _ = finiteExpectation (cylinderProbability M).weight (ActivePairCount.value F (fun x ↦ startIndicator x L)) := by
      simpa only [id_eq] using integral_eq_finite F hcut id
    _ = _ := finite_mean_eq F hcut

theorem probability_eq_finite {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    probability F L = finiteExpectation (cylinderProbability M).weight
      (fun σ ↦ if 0 < ActivePairCount.value F (fun x ↦ startIndicator x L) σ then 1 else 0) := by
  calc
    _ = infiniteRademacherMeasure.real {ω | 0 < ActivePairCount.value F
        (fun x ↦ startIndicator x L) (restrictToFinite M ω)} := by
      unfold probability
      congr 1
      ext ω
      change 0 < value F L ω ↔ 0 < ActivePairCount.value F (fun x ↦ startIndicator x L) (restrictToFinite M ω)
      rw [value_restrict F hcut ω]
    _ = _ := infiniteCylinder_event M (fun σ ↦ 0 < ActivePairCount.value F (fun x ↦ startIndicator x L) σ)

theorem probability_le_mass {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    probability F L ≤ ∑ e ∈ F, infiniteJointMoment L e := by
  rw [probability_eq_finite F hcut, ← finite_mean_eq F hcut]
  apply finiteExpectation_mono
  intro σ
  simpa only [← ActivePairCount.active_iff_positive] using
    ActivePairCount.indicator_le_value F (fun x ↦ startIndicator x L) σ

theorem truncation {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    (F : Finset (Finset ℕ)) (hF : F ⊆ G.powersetCard 2) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hm : 2 ≤ m) :
    (∑ e ∈ F, infiniteJointMoment L e) ≤ R ^ 2 * probability F L +
      CountObservables.countMoment G L m / R ^ (m - 2) := by
  let M := dyadicCutoff N L
  have hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff hG x ((mem_powersetCard.mp (hF he)).1 hx)
  rw [← finite_mean_eq F hcut, probability_eq_finite F hcut,
    CountObservables.countMoment_eq_finite hG]
  exact ActivePairCount.truncation (cylinderProbability M)
    (ActivePairCount.value F (fun x ↦ startIndicator x L))
    (fun σ ↦ (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ))
    (ActivePairCount.value_nonneg F _) (fun _ ↦ Nat.cast_nonneg _)
    (ActivePairCount.value_le_count_square G F hF _) R hR m hm

end PaperP1.ActiveEdgeObservables
