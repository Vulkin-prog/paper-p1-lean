module

public import PaperP1.Model.SourceConditionalDeviations

/-! # The fresh conditional mean is an actual conditional Bochner expectation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceConditionalCountMean

open Finset MeasureTheory PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.JointBranchingEvents PaperP1.SourceConditionalDeviations

local instance sourceConditionalCountMeanDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem weighted_count_integral (A G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (∫ ω, if ω ∈ jointEvent A L then (infiniteStartCount (G \ A) L ω : ℝ) else 0
      ∂infiniteRademacherMeasure) = ∑ z ∈ G \ A, infiniteJointMoment L (insert z A) := by
  have hfun : (fun ω ↦ if ω ∈ jointEvent A L then (infiniteStartCount (G \ A) L ω : ℝ) else 0) =
      (fun ω ↦ ∑ z ∈ G \ A, if ω ∈ jointEvent (insert z A) L then (1 : ℝ) else 0) := by
    funext ω
    by_cases ha : ω ∈ jointEvent A L
    · simp only [ha, ite_true, infiniteStartCount, indicatorCount, Nat.cast_sum]
      apply sum_congr rfl
      intro z _
      have hj : ω ∈ jointEvent (insert z A) L ↔ StartEvent (infiniteValueBit ω) z L := by
        change (∀ x ∈ insert z A, StartEvent (infiniteValueBit ω) x L) ↔ _
        rw [forall_mem_insert]
        exact and_iff_left ha
      by_cases hz : StartEvent (infiniteValueBit ω) z L <;>
        simp only [infiniteStartIndicator, hj, hz, decide_true, decide_false,
          Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, ite_true, ite_false]
    · have hj (z : ℕ) : ω ∉ jointEvent (insert z A) L := by
        intro h
        apply ha
        intro x hx
        exact h x (mem_insert_of_mem hx)
      simp only [ha, hj, ite_false, sum_const_zero]
  have hint (z : ℕ) : Integrable
      (fun ω ↦ if ω ∈ jointEvent (insert z A) L then (1 : ℝ) else 0) infiniteRademacherMeasure := by
    exact (integrable_const (1 : ℝ)).indicator (measurable_jointEvent (insert z A) hL)
  rw [hfun, integral_finsetSum _ (fun z _ ↦ hint z)]
  apply sum_congr rfl
  intro z _
  change (∫ ω, (jointEvent (insert z A) L).indicator (1 : InfiniteSample → ℝ) ω
    ∂infiniteRademacherMeasure) = _
  rw [integral_indicator_one (measurable_jointEvent (insert z A) hL)]
  exact (infiniteJointMoment_eq_probability (insert z A) hL).symm

theorem freshMean_eq_conditional_integral (N L : ℕ) (A : Finset ℕ) (hL : 0 < L) :
    freshMean N L A =
      (∫ ω, if ω ∈ jointEvent A L then (infiniteStartCount (dyadicBlock N \ A) L ω : ℝ) else 0
        ∂infiniteRademacherMeasure) / infiniteRademacherMeasure.real (jointEvent A L) := by
  rw [weighted_count_integral A (dyadicBlock N) L hL, ← infiniteJointMoment_eq_probability A hL, sum_div]
  rfl

theorem fresh_count_on_source (A G : Finset ℕ) (L : ℕ) (hA : A ⊆ G)
    (ω : InfiniteSample) (ha : ω ∈ jointEvent A L) :
    (infiniteStartCount (G \ A) L ω : ℝ) = (infiniteStartCount G L ω : ℝ) - A.card := by
  have hsource : infiniteStartCount A L ω = A.card := by
    unfold infiniteStartCount indicatorCount
    calc
      _ = ∑ _x ∈ A, (1 : ℕ) := by
        apply sum_congr rfl
        intro x hx
        simp only [infiniteStartIndicator, ha x hx, decide_true, Bool.toNat_true]
      _ = _ := by simp
  have hsum := sum_sdiff (f := fun x ↦ (infiniteStartIndicator x L ω).toNat) hA
  change infiniteStartCount (G \ A) L ω + infiniteStartCount A L ω = infiniteStartCount G L ω at hsum
  rw [hsource] at hsum
  have hreal : (infiniteStartCount (G \ A) L ω : ℝ) + A.card = (infiniteStartCount G L ω : ℝ) := by
    exact_mod_cast hsum
  linarith only [hreal]

theorem freshMean_eq_full_minus_source_integral (N L : ℕ) (A : Finset ℕ)
    (hL : 0 < L) (hA : A ⊆ dyadicBlock N) :
    freshMean N L A =
      (∫ ω, if ω ∈ jointEvent A L then (infiniteStartCount (dyadicBlock N) L ω : ℝ) - A.card else 0
        ∂infiniteRademacherMeasure) / infiniteRademacherMeasure.real (jointEvent A L) := by
  rw [freshMean_eq_conditional_integral N L A hL]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ by
    by_cases ha : ω ∈ jointEvent A L
    · simp only [ha, ite_true, fresh_count_on_source A (dyadicBlock N) L hA ω ha]
    · simp only [ha, ite_false]

end PaperP1.SourceConditionalCountMean
