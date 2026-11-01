module

public import PaperP1.Probability.AtomicProbability
public import Mathlib.Tactic.Linarith

/-! # Bounded tests and an attained total-variation test on the naturals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AtomicTests

open MeasureTheory PaperP1.AtomicProbability

def expectation (P : ProbabilityMeasure ℕ) (h : ℕ → ℝ) : ℝ := ∑' k, realMass P k * h k

theorem of_realMass_eq (P : ProbabilityMeasure ℕ) :
    ofMass (realMass P) (realMass_nonneg P) (hasSum_realMass P) = P := by
  apply Subtype.ext
  change (ofMass (realMass P) (realMass_nonneg P) (hasSum_realMass P) : Measure ℕ) = (P : Measure ℕ)
  apply Measure.ext_of_measureReal_singleton
  intro k
  exact ofMass_real_singleton _ _ _ _

theorem integrable_iff_summable (P : ProbabilityMeasure ℕ) (h : ℕ → ℝ) :
    Integrable h (P : Measure ℕ) ↔ Summable (fun k ↦ realMass P k * |h k|) := by
  have hmeasure : (ofMass (realMass P) (realMass_nonneg P) (hasSum_realMass P) : Measure ℕ) = (P : Measure ℕ) :=
    congrArg (fun Q : ProbabilityMeasure ℕ ↦ (Q : Measure ℕ)) (of_realMass_eq P)
  rw [← hmeasure]
  exact ofMass_integrable_iff _ _ _ h

theorem expectation_eq_integral (P : ProbabilityMeasure ℕ) (h : ℕ → ℝ) (hh : Integrable h (P : Measure ℕ)) :
    expectation P h = ∫ k, h k ∂(P : Measure ℕ) := by
  simpa only [expectation, realMass, smul_eq_mul] using (integral_countable hh).symm

theorem summable_mul_unit {ι : Type*} {a h : ι → ℝ} (ha : Summable a) (hh : ∀ k, |h k| ≤ 1) :
    Summable (fun k ↦ a k * h k) := by
  apply ha.abs.of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hh k)

theorem summable_mul_bounded {ι : Type*} {a h : ι → ℝ} (ha : Summable a) {M : ℝ} (hh : ∀ k, |h k| ≤ M) :
    Summable (fun k ↦ a k * h k) := by
  apply (ha.abs.mul_right M).of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hh k) (abs_nonneg _)

theorem abs_tsum_mul_unit {ι : Type*} {a h : ι → ℝ} (ha : Summable a) (hh : ∀ k, |h k| ≤ 1) :
    |∑' k, a k * h k| ≤ ∑' k, |a k| := by
  have hs := summable_mul_unit ha hh
  have hnorm : |∑' k, a k * h k| ≤ ∑' k, |a k * h k| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  exact hnorm.trans (hs.abs.tsum_le_tsum (fun k ↦ by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hh k)) ha.abs)

theorem expectation_sub (P Q : ProbabilityMeasure ℕ) (h : ℕ → ℝ) {M : ℝ} (hh : ∀ k, |h k| ≤ M) :
    expectation P h - expectation Q h = ∑' k, (realMass P k - realMass Q k) * h k := by
  unfold expectation
  rw [← (summable_mul_bounded (hasSum_realMass P).summable hh).tsum_sub
    (summable_mul_bounded (hasSum_realMass Q).summable hh)]
  exact tsum_congr (fun k ↦ by ring)

theorem unit_expectation_difference (P Q : ProbabilityMeasure ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |expectation P h - expectation Q h| ≤ 2 * totalVariation P Q := by
  rw [expectation_sub P Q h hh]
  have hb := abs_tsum_mul_unit ((hasSum_realMass P).summable.sub (hasSum_realMass Q).summable) hh
  change |∑' k, (realMass P k - realMass Q k) * h k| ≤ _ at hb
  calc
    _ ≤ ∑' k, |realMass P k - realMass Q k| := hb
    _ = _ := by unfold totalVariation realMass; ring

def attainingTest (P Q : ProbabilityMeasure ℕ) (k : ℕ) : ℝ := if realMass Q k ≤ realMass P k then 1 else 0

theorem attainingTest_bounds (P Q : ProbabilityMeasure ℕ) (k : ℕ) :
    0 ≤ attainingTest P Q k ∧ attainingTest P Q k ≤ 1 := by
  unfold attainingTest
  split_ifs <;> norm_num

theorem attainingTest_difference (P Q : ProbabilityMeasure ℕ) :
    expectation P (attainingTest P Q) - expectation Q (attainingTest P Q) = totalVariation P Q := by
  have ht : ∀ k, |attainingTest P Q k| ≤ 1 := fun k ↦ by
    rw [abs_of_nonneg (attainingTest_bounds P Q k).1]
    exact (attainingTest_bounds P Q k).2
  rw [expectation_sub P Q _ ht]
  let a : ℕ → ℝ := fun k ↦ realMass P k - realMass Q k
  have ha := (hasSum_realMass P).sub (hasSum_realMass Q)
  have hzero : HasSum a 0 := by simpa only [a, sub_self] using ha
  have hs := summable_mul_unit hzero.summable ht
  have hid : ∀ k, 2 * (a k * attainingTest P Q k) = |a k| + a k := by
    intro k
    unfold a attainingTest
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
      ring
  have heq : 2 * (∑' k, a k * attainingTest P Q k) = (∑' k, |a k|) := by
    rw [← tsum_mul_left]
    calc
      _ = ∑' k, (|a k| + a k) := tsum_congr hid
      _ = _ := by rw [hzero.summable.abs.tsum_add hzero.summable, hzero.tsum_eq, add_zero]
  change (∑' k, a k * attainingTest P Q k) = _
  change _ = (∑' k, |a k|) / 2
  linarith

theorem totalVariation_le_of_tests (P Q : ProbabilityMeasure ℕ) {D : ℝ}
    (hbound : ∀ h : ℕ → ℝ, (∀ k, 0 ≤ h k ∧ h k ≤ 1) → |expectation P h - expectation Q h| ≤ D) :
    totalVariation P Q ≤ D := by
  have h := hbound (attainingTest P Q) (attainingTest_bounds P Q)
  rw [attainingTest_difference, abs_of_nonneg (totalVariation_nonneg P Q)] at h
  exact h

end PaperP1.AtomicTests
