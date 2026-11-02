module

public import PaperP1.Probability.AtomicProbability
public import Mathlib.Tactic.Linarith

/-! # Actual total-variation triangle inequalities and reference stability -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AtomicProbabilityMetric

open MeasureTheory PaperP1.AtomicProbability

theorem triangle (P Q R : ProbabilityMeasure ℕ) :
    totalVariation P R ≤ totalVariation P Q + totalVariation Q R := by
  have hP := (hasSum_realMass P).summable
  have hQ := (hasSum_realMass Q).summable
  have hR := (hasSum_realMass R).summable
  have h := (hP.sub hR).abs.tsum_le_tsum
    (fun k ↦ abs_sub_le (realMass P k) (realMass Q k) (realMass R k))
    ((hP.sub hQ).abs.add (hQ.sub hR).abs)
  rw [(hP.sub hQ).abs.tsum_add (hQ.sub hR).abs] at h
  change (∑' k, |realMass P k - realMass R k|) / 2 ≤
    (∑' k, |realMass P k - realMass Q k|) / 2 + (∑' k, |realMass Q k - realMass R k|) / 2
  linarith only [h]

theorem reference_stability (P Q R : ProbabilityMeasure ℕ) :
    |totalVariation P Q - totalVariation P R| ≤ totalVariation Q R := by
  have h1 := triangle P R Q
  have h2 := triangle P Q R
  rw [totalVariation_symm R Q] at h1
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

theorem signed_distance (P Q : ProbabilityMeasure ℕ) :
    (∑' k : ℕ, |((P : Measure ℕ).toSignedMeasure - (Q : Measure ℕ).toSignedMeasure) {k}|) =
      2 * totalVariation P Q := by
  have heq (k : ℕ) :
      ((P : Measure ℕ).toSignedMeasure - (Q : Measure ℕ).toSignedMeasure) {k} = realMass P k - realMass Q k := by
    rw [_root_.sub_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k),
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
    rfl
  simp_rw [heq]
  change (∑' k, |realMass P k - realMass Q k|) = 2 * ((∑' k, |realMass P k - realMass Q k|) / 2)
  ring

theorem reference_stability_signed (P Q R : ProbabilityMeasure ℕ) :
    |totalVariation P Q - totalVariation P R| ≤
      (∑' k : ℕ, |((Q : Measure ℕ).toSignedMeasure - (R : Measure ℕ).toSignedMeasure) {k}|) / 2 := by
  rw [signed_distance]
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using reference_stability P Q R

end PaperP1.AtomicProbabilityMetric
