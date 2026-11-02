module

public import PaperP1.Model.ActiveEdgeObservables

/-! # The second factorial moment of any actual active-family count is its ordered union joint sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveFamilySecondMoment

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher

local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι Ω : Type*} [DecidableEq ι]

def ordered (F : Finset (Finset ι)) : Finset (Finset ι × Finset ι) := (F ×ˢ F).filter fun p ↦ p.1 ≠ p.2

theorem union_product (e f : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (∏ x ∈ e ∪ f, (indicatorValue (J x ω) : ℝ)) =
      (∏ x ∈ e, (indicatorValue (J x ω) : ℝ)) * (∏ x ∈ f, (indicatorValue (J x ω) : ℝ)) := by
  simp only [indicator_product_eq_indicator]
  have hiff : (∀ x ∈ e ∪ f, J x ω = true) ↔ (∀ x ∈ e, J x ω = true) ∧ (∀ x ∈ f, J x ω = true) := by
    constructor
    · intro h
      exact ⟨fun x hx ↦ h x (mem_union_left _ hx), fun x hx ↦ h x (mem_union_right _ hx)⟩
    · intro h x hx
      rcases mem_union.mp hx with hxe | hxf
      · exact h.1 x hxe
      · exact h.2 x hxf
  by_cases he : ∀ x ∈ e, J x ω = true
  · by_cases hf : ∀ x ∈ f, J x ω = true
    · have hu := hiff.mpr ⟨he, hf⟩
      rw [ite_eq_left hu, ite_eq_left he, ite_eq_left hf, mul_one]
    · have hu : ¬∀ x ∈ e ∪ f, J x ω = true := fun h ↦ hf (hiff.mp h).2
      rw [ite_eq_right hu, ite_eq_right hf, mul_zero]
  · have hu : ¬∀ x ∈ e ∪ f, J x ω = true := fun h ↦ he (hiff.mp h).1
    rw [ite_eq_right hu, ite_eq_right he, zero_mul]

theorem factorial_value (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) :
    ActivePairCount.value F J ω ^ 2 - ActivePairCount.value F J ω =
      ∑ p ∈ ordered F, ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ) := by
  have hfull : ActivePairCount.value F J ω ^ 2 =
      ∑ p ∈ F ×ˢ F, ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ) := by
    rw [ActivePairCount.value, pow_two, sum_mul_sum, sum_product]
    apply sum_congr rfl
    intro e _he
    exact sum_congr rfl (fun f _ ↦ (union_product e f J ω).symm)
  have hdiag : (∑ p ∈ (F ×ˢ F).filter (fun p ↦ ¬p.1 ≠ p.2),
      ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ)) = ActivePairCount.value F J ω := by
    rw [sum_filter, sum_product, ActivePairCount.value]
    apply sum_congr rfl
    intro e he
    simp only [not_not]
    simp [he]
  have hsplit := sum_filter_add_sum_filter_not (F ×ˢ F) (fun p ↦ p.1 ≠ p.2)
    (fun p ↦ ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ))
  change (∑ p ∈ ordered F, ∏ x ∈ p.1 ∪ p.2, (indicatorValue (J x ω) : ℝ)) + _ = _ at hsplit
  rw [hdiag, ← hfull] at hsplit
  linarith only [hsplit]

theorem infinite_mean_eq {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    (∫ ω, (ActiveEdgeObservables.value F L ω ^ 2 - ActiveEdgeObservables.value F L ω) ∂infiniteRademacherMeasure) =
      ∑ p ∈ ordered F, infiniteJointMoment L (p.1 ∪ p.2) := by
  calc
    _ = finiteExpectation (cylinderProbability M).weight
        (fun σ ↦ ActivePairCount.value F (fun x ↦ startIndicator x L) σ ^ 2 -
          ActivePairCount.value F (fun x ↦ startIndicator x L) σ) :=
      ActiveEdgeObservables.integral_eq_finite F hcut (fun x ↦ x ^ 2 - x)
    _ = finiteExpectation (cylinderProbability M).weight
        (fun σ ↦ ∑ p ∈ ordered F, ∏ x ∈ p.1 ∪ p.2, (indicatorValue (startIndicator x L σ) : ℝ)) := by
      congr 1
      funext σ
      exact factorial_value F (fun x ↦ startIndicator x L) σ
    _ = ∑ p ∈ ordered F, finiteJointMoment (cylinderProbability M) (fun x ↦ startIndicator x L) (p.1 ∪ p.2) :=
      finiteExpectation_sum _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨he, hf⟩ := mem_product.mp (mem_filter.mp hp).1
      symm
      apply infiniteJointMoment_eq_finite
      intro x hx
      rcases mem_union.mp hx with hxe | hxf
      · exact hcut p.1 he x hxe
      · exact hcut p.2 hf x hxf

end PaperP1.ActiveFamilySecondMoment
