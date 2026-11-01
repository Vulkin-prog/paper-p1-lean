module

public import PaperP1.Algebra.CharlierRoots
public import PaperP1.Analysis.FiniteNegativeMass
public import PaperP1.Probability.PoissonDifferenceSigned

/-! # The exact four-mass norm formula, including integer-root endpoints -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonSecondDifferenceNorm

open Finset PaperP1.PoissonSequence PaperP1.FiniteShiftAction PaperP1.IteratedPoissonDifferences
  PaperP1.CharlierRoots PaperP1.CharlierQuadratic PaperP1.FiniteNegativeMass PaperP1.PoissonDifferenceSigned

theorem difference_two_eq_secondDifference (a : ℕ → ℝ) : difference 2 a = secondDifference a := by
  rw [show 2 = 1 + 1 from rfl, difference_succ, difference_succ, difference_zero]
  funext k
  cases k with
  | zero => simp only [Pi.sub_apply, shift_zero, secondDifference]; ring
  | succ k => simp only [Pi.sub_apply, shift_succ, secondDifference]; ring

theorem negative_support (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    secondDifference (mass μ) k < 0 ↔ k ∈ Icc (lowerIndex μ) (upperIndex μ) := by
  rw [secondDifference_mass μ hμ.ne']
  have hc : 0 < mass μ k / μ ^ 2 := div_pos (mass_pos μ hμ k) (by positivity)
  change mass μ k / μ ^ 2 * quadratic μ k < 0 ↔ _
  rw [mul_neg_iff]
  simp only [hc, true_and, not_lt_of_ge hc.le, false_and, or_false]
  exact quadratic_neg_iff_indices μ hμ k

theorem four_mass_formula (μ : ℝ) (hμ : 0 < μ) :
    norm μ 2 = 2 * (extended (mass μ) ((lowerIndex μ : ℤ) - 1) -
      extended (mass μ) ((lowerIndex μ : ℤ) - 2) +
      extended (mass μ) ((upperIndex μ : ℤ) - 1) - mass μ (upperIndex μ)) := by
  rw [norm_eq_l1 μ hμ.le 2, difference_two_eq_secondDifference]
  have hl1 := l1_eq_negative_sum (secondDifference (mass μ))
    (hasSum_secondDifference (hasSum_mass μ hμ.le))
    (Icc (lowerIndex μ) (upperIndex μ)) (negative_support μ hμ)
  rw [hl1, secondDifference_interval_sum _ _ _ (indices_bounds μ hμ).1 (indices_bounds μ hμ).2]
  rw [shift_eq_extended, shift_eq_extended, second_shift_eq_extended]
  ring

theorem norm_second_lower_bound (μ : ℝ) (hμ : 0 ≤ μ) : 2 * Real.exp (-μ) ≤ norm μ 2 := by
  rw [norm_eq_l1 μ hμ 2, difference_two_eq_secondDifference]
  have h := l1_ge_twice_point (secondDifference (mass μ))
    (hasSum_secondDifference (hasSum_mass μ hμ)) 0
  simpa only [secondDifference, shift_zero, mul_zero, sub_zero, zero_add, mass, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using h

theorem coefficient_lower_bound (μ : ℝ) (hμ : 0 ≤ μ) :
    Real.exp (-μ) / 2 ≤ correctionCoefficient μ := by
  unfold correctionCoefficient
  have h := norm_second_lower_bound μ hμ
  linarith

theorem norm_at_two : norm 2 2 = 10 / (3 * Real.exp 2) := by
  have hroot : Real.sqrt (9 : ℝ) = 3 := by
    have h := Real.sqrt_sq_eq_abs (3 : ℝ)
    norm_num at h
    exact h
  have hlo : lowerIndex 2 = 2 := by norm_num [lowerIndex, lowerRoot, hroot]
  have hup : upperIndex 2 = 3 := by norm_num [upperIndex, upperRoot, hroot]
  have h := four_mass_formula 2 (by norm_num)
  rw [hlo, hup] at h
  norm_num [extended, mass] at h
  rw [Real.exp_neg] at h
  rw [h]
  field_simp
  norm_num

theorem coefficient_at_two : correctionCoefficient 2 = 5 / (6 * Real.exp 2) := by
  rw [correctionCoefficient, norm_at_two]
  ring

theorem norm_at_two_exp_one : norm 2 2 = 10 / (3 * (Real.exp 1) ^ 2) := by
  rw [← Real.exp_nat_mul, mul_one]
  exact norm_at_two

theorem coefficient_at_two_exp_one : correctionCoefficient 2 = 5 / (6 * (Real.exp 1) ^ 2) := by
  rw [← Real.exp_nat_mul, mul_one]
  exact coefficient_at_two

/-- All three conclusions of article Proposition 19.2, with actual signed measures. -/
theorem main_19_2 (μ : ℝ) (hμ : 0 < μ) :
    (norm μ 2 = 2 * (extended (mass μ) ((lowerIndex μ : ℤ) - 1) -
      extended (mass μ) ((lowerIndex μ : ℤ) - 2) +
      extended (mass μ) ((upperIndex μ : ℤ) - 1) - mass μ (upperIndex μ))) ∧
    (∀ r : ℕ, norm μ r ≤ min ((2 : ℝ) ^ r) (Real.sqrt (r.factorial : ℝ) / μ ^ ((r : ℝ) / 2))) ∧
    norm 2 2 = 10 / (3 * Real.exp 2) ∧ correctionCoefficient 2 = 5 / (6 * Real.exp 2) :=
  ⟨four_mass_formula μ hμ, norm_all_orders μ hμ, norm_at_two, coefficient_at_two⟩

end PaperP1.PoissonSecondDifferenceNorm
