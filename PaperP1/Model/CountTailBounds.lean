module

public import PaperP1.Model.FactorialBranching
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Actual count tails and their finite falling-factorial Markov bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CountTailBounds

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.FactorialCountMoments PaperP1.CountObservables
  PaperP1.Algebra PaperP1.Probability

local instance countTailDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance countTailMeasurableF2 : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

def probability (N L : ℕ) (b : ℝ) : ℝ :=
  infiniteRademacherMeasure.real {ω | b < (infiniteStartCount (dyadicBlock N) L ω : ℝ)}

def moment (N L : ℕ) (b : ℝ) (r : ℕ) : ℝ :=
  ∫ ω, if b < (infiniteStartCount (dyadicBlock N) L ω : ℝ) then
    (infiniteStartCount (dyadicBlock N) L ω : ℝ) ^ r else 0 ∂infiniteRademacherMeasure

theorem probability_nonneg (N L : ℕ) (b : ℝ) : 0 ≤ probability N L b := measureReal_nonneg

theorem probability_mono {N L : ℕ} {a b : ℝ} (hba : b ≤ a) : probability N L a ≤ probability N L b :=
  measureReal_mono (fun _ h ↦ hba.trans_lt h)

theorem probability_eq_finite (N L : ℕ) (b : ℝ) :
    probability N L b = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ if b < (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) then 1 else 0) := by
  have hmeas : MeasurableSet {ω | b < (infiniteStartCount (dyadicBlock N) L ω : ℝ)} :=
    (measurable_infiniteStartCount (dyadicBlock N) L)
      ((Set.to_countable {n : ℕ | b < (n : ℝ)}).measurableSet)
  unfold probability
  rw [← integral_indicator_one hmeas]
  change (∫ ω, if b < (infiniteStartCount (dyadicBlock N) L ω : ℝ) then (1 : ℝ) else 0 ∂infiniteRademacherMeasure) = _
  exact count_observable_integral_eq_finite (subset_refl _) (fun n : ℕ ↦ if b < (n : ℝ) then 1 else 0)

theorem moment_eq_finite (N L : ℕ) (b : ℝ) (r : ℕ) :
    moment N L b r = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ if b < (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) then
        (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) ^ r else 0) :=
  count_observable_integral_eq_finite (subset_refl _) (fun n : ℕ ↦ if b < (n : ℝ) then (n : ℝ) ^ r else 0)

theorem descFactorial_lower (n k : ℕ) (hkn : 2 * k ≤ n) :
    ((n : ℝ) / 2) ^ k ≤ (n.descFactorial k : ℝ) := by
  rw [cast_descFactorial_eq_falling_product]
  have hprod : ((n : ℝ) / 2) ^ k = ∏ _i ∈ range k, (n : ℝ) / 2 := by simp [div_pow]
  rw [hprod]
  apply prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    have hiR : (i : ℝ) < k := by exact_mod_cast mem_range.mp hi
    have hknR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith

theorem falling_markov_product (N L k : ℕ) {b : ℝ} (hb : 0 ≤ b) (hkb : 2 * (k : ℝ) ≤ b) :
    (b / 2) ^ k * probability N L b ≤ factorialCountMoment (dyadicBlock N) L k := by
  rw [probability_eq_finite, factorialCountMoment_eq_finite (subset_refl _) k, ← finiteExpectation_const_mul]
  unfold finiteExpectation
  apply sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_left _ ((cylinderProbability (dyadicCutoff N L)).weight_nonneg σ)
  let n := indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ
  change (b / 2) ^ k * (if b < (n : ℝ) then 1 else 0) ≤ (n.descFactorial k : ℝ)
  split_ifs with hbn
  · rw [mul_one]
    have hkn : 2 * k ≤ n := by exact_mod_cast (hkb.trans hbn.le)
    exact (pow_le_pow_left₀ (div_nonneg hb (by norm_num)) (by linarith : b / 2 ≤ (n : ℝ) / 2) k).trans
      (descFactorial_lower n k hkn)
  · rw [mul_zero]
    exact Nat.cast_nonneg _

theorem probability_le_power (N L k : ℕ) {b M : ℝ} (hb : 0 < b) (hkb : 2 * (k : ℝ) ≤ b)
    (hM : factorialCountMoment (dyadicBlock N) L k ≤ M ^ k) :
    probability N L b ≤ (2 * M / b) ^ k := by
  have hproduct := (falling_markov_product N L k hb.le hkb).trans hM
  have hdiv : probability N L b ≤ M ^ k / (b / 2) ^ k := by
    apply (le_div_iff₀ (pow_pos (div_pos hb (by norm_num)) k)).mpr
    simpa only [mul_comm] using hproduct
  calc
    _ ≤ M ^ k / (b / 2) ^ k := hdiv
    _ = _ := by rw [← div_pow]; congr 1; field_simp

theorem moment_le_count_power (N L : ℕ) (b : ℝ) (r : ℕ) :
    moment N L b r ≤ (N : ℝ) ^ r * probability N L b := by
  rw [moment_eq_finite, probability_eq_finite, ← finiteExpectation_const_mul]
  unfold finiteExpectation
  apply sum_le_sum
  intro σ _
  apply mul_le_mul_of_nonneg_left _ ((cylinderProbability (dyadicCutoff N L)).weight_nonneg σ)
  change (if b < (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) then
    (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) ^ r else 0) ≤
    (N : ℝ) ^ r * (if b < (indicatorCount (dyadicBlock N) (fun x ↦ startIndicator x L) σ : ℝ) then 1 else 0)
  split_ifs
  · rw [mul_one]
    have hcount := indicatorCount_le_card (dyadicBlock N) (fun x ↦ startIndicator x L) σ
    have hcard : (dyadicBlock N).card = N := by simp only [dyadicBlock, Nat.card_Ico, two_mul, Nat.add_sub_cancel_left]
    rw [hcard] at hcount
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcount) r
  · rw [mul_zero]

end PaperP1.CountTailBounds
