module

public import PaperP1.Model.HeterogeneousDirectMaximum
public import PaperP1.Model.CountObservables

/-! # Exact shifted positive count-envelope moments and an elementary power bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedCountMoments

open MeasureTheory Finset PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.HeterogeneousDirectMaximum

def moment (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∫ ω, ((infiniteStartCount G L ω : ℝ) + actualMean G L) ^ r ∂infiniteRademacherMeasure

theorem add_power_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    (a + b) ^ r ≤ 2 ^ r * (a ^ r + b ^ r) := by
  have hsum : a + b ≤ 2 * max a b := by have h1 := le_max_left a b; have h2 := le_max_right a b; linarith
  have hp := pow_le_pow_left₀ (add_nonneg ha hb) hsum r
  rw [mul_pow] at hp
  have hm : (max a b) ^ r ≤ a ^ r + b ^ r := by
    by_cases hab : a ≤ b
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (pow_nonneg ha r)
    · rw [max_eq_left (le_of_not_ge hab)]
      exact le_add_of_nonneg_right (pow_nonneg hb r)
  exact hp.trans (mul_le_mul_of_nonneg_left hm (by positivity))

theorem eq_finite {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    moment G L r = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ ((indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) + actualMean G L) ^ r) :=
  CountObservables.count_observable_integral_eq_finite hG (fun n ↦ ((n : ℝ) + actualMean G L) ^ r)

theorem finite_upper {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    moment G L r ≤ 2 ^ r * (CountObservables.countMoment G L r + actualMean G L ^ r) := by
  rw [eq_finite hG, CountObservables.countMoment_eq_finite hG]
  have hmean : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  calc
    _ ≤ finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ 2 ^ r * ((indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) ^ r + actualMean G L ^ r)) := by
      apply sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left
        (add_power_bound _ _ (Nat.cast_nonneg _) hmean r) ((cylinderProbability _).weight_nonneg σ)
    _ = _ := by
      rw [finiteExpectation_const_mul, finiteExpectation_add, finiteExpectation_const,
        (cylinderProbability _).total_weight, one_mul]

end PaperP1.ShiftedCountMoments
