module

public import PaperP1.Probability.IteratedPoissonDifferences
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A closed diagonal Charlier identity and the sharp general Poisson difference bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CharlierDifferenceNorm

open Finset PaperP1.Probability PaperP1.PoissonSequence PaperP1.FiniteShiftAction
  PaperP1.IteratedPoissonDifferences PaperP1.DifferenceCoefficients

def charlier (μ : ℝ) (r k : ℕ) : ℝ := ∑ j ∈ range (r + 1),
  ((forwardDifference : SignedLaw ℝ) ^ r).coeff j / μ ^ j * (k.descFactorial j : ℝ)

theorem difference_eq_mass_mul_charlier (μ : ℝ) (hμ : μ ≠ 0) (r k : ℕ) :
    difference r (mass μ) k = mass μ k * charlier μ r k := by
  rw [difference_apply_range]
  unfold charlier
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [shiftBy_mass μ hμ]
  ring

theorem factorial_coefficient_sum (μ : ℝ) (r : ℕ) :
    (∑ j ∈ range (r + 1), ((forwardDifference : SignedLaw ℝ) ^ r).coeff j / μ ^ j *
      ((j.descFactorial r : ℝ) * μ ^ (j - r))) = (r.factorial : ℝ) / μ ^ r := by
  rw [sum_eq_single r]
  · rw [forwardDifference_pow_coeff, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
      mul_one, Nat.descFactorial_self, pow_zero, mul_one]
    ring
  · intro j hj hjr
    have hlt : j < r := by have h := mem_range.mp hj; omega
    rw [Nat.descFactorial_of_lt hlt, Nat.cast_zero, zero_mul, mul_zero]
  · intro h
    exact False.elim (h (mem_range.mpr (by omega)))

theorem hasSum_charlier_square (μ : ℝ) (hμ : 0 < μ) (r : ℕ) :
    HasSum (fun k : ℕ ↦ mass μ k * charlier μ r k ^ 2) ((r.factorial : ℝ) / μ ^ r) := by
  have hterm (j : ℕ) : HasSum (fun k : ℕ ↦
      ((forwardDifference : SignedLaw ℝ) ^ r).coeff j / μ ^ j *
        (difference r (mass μ) k * (k.descFactorial j : ℝ)))
      (((forwardDifference : SignedLaw ℝ) ^ r).coeff j / μ ^ j *
        ((j.descFactorial r : ℝ) * μ ^ (j - r))) :=
    (hasSum_difference_factorial μ hμ.le r j).mul_left _
  have hs := hasSum_sum (s := range (r + 1)) (fun j _ ↦ hterm j)
  rw [factorial_coefficient_sum] at hs
  convert hs using 1
  funext k
  calc
    _ = difference r (mass μ) k * charlier μ r k := by
      rw [difference_eq_mass_mul_charlier μ hμ.ne']
      ring
    _ = _ := by
      unfold charlier
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

theorem l1_le_sqrt_factorial_ratio (μ : ℝ) (hμ : 0 < μ) (r : ℕ) :
    l1 (difference r (mass μ)) ≤ Real.sqrt ((r.factorial : ℝ) / μ ^ r) := by
  let K : ℝ := (r.factorial : ℝ) / μ ^ r
  have hK : 0 < K := by unfold K; positivity
  have hsqrt : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hsqrtpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hleft := (summable_difference r (mass μ) (hasSum_mass μ hμ.le).summable).abs.hasSum.mul_left (2 * Real.sqrt K)
  have hright := (hasSum_charlier_square μ hμ r).add ((hasSum_mass μ hμ.le).mul_left K)
  have hpoint (k : ℕ) : 2 * Real.sqrt K * |difference r (mass μ) k| ≤
      mass μ k * charlier μ r k ^ 2 + K * mass μ k := by
    have hm := (mass_pos μ hμ k).le
    have hquad : 2 * Real.sqrt K * |charlier μ r k| ≤ charlier μ r k ^ 2 + K := by
      nlinarith [sq_nonneg (|charlier μ r k| - Real.sqrt K), sq_abs (charlier μ r k)]
    have h := mul_le_mul_of_nonneg_left hquad hm
    rw [difference_eq_mass_mul_charlier μ hμ.ne', abs_mul, abs_of_nonneg hm]
    nlinarith
  have hsum := hleft.summable.tsum_le_tsum hpoint hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at hsum
  change 2 * Real.sqrt K * l1 (difference r (mass μ)) ≤ K + K * 1 at hsum
  nlinarith

theorem sqrt_factorial_ratio (μ : ℝ) (hμ : 0 < μ) (r : ℕ) :
    Real.sqrt ((r.factorial : ℝ) / μ ^ r) = Real.sqrt (r.factorial : ℝ) / μ ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_div (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
  congr 1
  ring

/-- The full all-order norm inequality from article Proposition 19.2. -/
theorem all_order_norm_bound (μ : ℝ) (hμ : 0 < μ) (r : ℕ) :
    l1 (difference r (mass μ)) ≤ min ((2 : ℝ) ^ r) (Real.sqrt (r.factorial : ℝ) / μ ^ ((r : ℝ) / 2)) := by
  apply le_min (l1_poisson_difference_le μ hμ.le r)
  rw [← sqrt_factorial_ratio μ hμ r]
  exact l1_le_sqrt_factorial_ratio μ hμ r

end PaperP1.CharlierDifferenceNorm
