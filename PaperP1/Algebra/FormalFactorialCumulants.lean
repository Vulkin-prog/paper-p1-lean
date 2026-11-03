module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Factorial cumulants from the actual formal logarithm, with a proved all-order moment recursion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalFactorialCumulants

open Finset PowerSeries

def moment (f : ℝ⟦X⟧) (r : ℕ) : ℝ := (r.factorial : ℝ) * coeff r f

def cumulant (f : ℝ⟦X⟧) (r : ℕ) : ℝ := moment (logOf f) r

theorem logarithmic_derivative (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) :
    derivative (logOf f) * f = derivative f := by
  have hz : constantCoeff (f - 1) = 0 := by rw [map_sub, map_one, hf, sub_self]
  have hg : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' hz
  have hOne : (1 : ℝ⟦X⟧).subst (f - 1) = 1 := by rw [← coe_substAlgHom hg, map_one]
  have hX : (X : ℝ⟦X⟧).subst (f - 1) = f - 1 := by rw [← coe_substAlgHom hg, substAlgHom_X]
  have hinv := congrArg (fun p : ℝ⟦X⟧ ↦ p.subst (f - 1)) (derivative_log_mul_one_add_X (A := ℝ))
  rw [subst_mul hg, subst_add hg, hOne, hX, show (1 : ℝ⟦X⟧) + (f - 1) = f by ring] at hinv
  rw [logOf_eq, derivative_subst hg, map_sub, derivative_one, sub_zero]
  calc
    _ = derivative f * ((derivative (PowerSeries.log ℝ)).subst (f - 1) * f) := by ring
    _ = _ := by rw [hinv, mul_one]

theorem moment_zero (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) : moment f 0 = 1 := by
  simpa only [moment, Nat.factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff] using hf

theorem cumulant_zero (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) : cumulant f 0 = 0 := by
  simpa only [cumulant, moment, Nat.factorial_zero, Nat.cast_one, one_mul, coeff_zero_eq_constantCoeff] using constantCoeff_logOf hf

theorem moment_succ (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) (n : ℕ) :
    moment f (n + 1) = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * cumulant f (i + 1) * moment f (n - i) := by
  have hc := congrArg (fun p : ℝ⟦X⟧ ↦ coeff n p) (logarithmic_derivative f hf)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij : ℕ × ℕ ↦ coeff ij.1 (derivative (logOf f)) * coeff ij.2 f) n] at hc
  simp only [coeff_derivative] at hc
  calc
    _ = (n.factorial : ℝ) * (coeff (n + 1) f * (n + 1)) := by
      rw [moment, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
    _ = (n.factorial : ℝ) * ∑ i ∈ range (n + 1),
        (coeff (i + 1) (logOf f) * (i + 1)) * coeff (n - i) f := by rw [hc]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hfact : (n.factorial : ℝ) = (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (show i ≤ n by have h := mem_range.mp hi; omega)).symm
      rw [hfact]
      simp only [cumulant, moment, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

theorem recurrence (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) (n : ℕ) :
    cumulant f (n + 1) = moment f (n + 1) -
      ∑ i ∈ range n, (n.choose i : ℝ) * cumulant f (i + 1) * moment f (n - i) := by
  have h := moment_succ f hf n
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, moment_zero f hf, mul_one] at h
  linarith only [h]

theorem cumulant_one (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) : cumulant f 1 = moment f 1 := by
  simpa only [Nat.zero_add, range_zero, sum_empty, sub_zero] using recurrence f hf 0

theorem cumulant_two (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) :
    cumulant f 2 = moment f 2 - moment f 1 ^ 2 := by
  have h := recurrence f hf 1
  simpa only [Nat.reduceAdd, range_one, sum_singleton, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.zero_add, Nat.sub_zero, cumulant_one f hf, pow_two] using h

theorem cumulant_three (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) :
    cumulant f 3 = moment f 3 - 3 * moment f 2 * moment f 1 + 2 * moment f 1 ^ 3 := by
  have h := recurrence f hf 2
  norm_num [sum_range_succ, cumulant_one f hf, cumulant_two f hf] at h
  rw [h]
  ring

theorem cumulant_four (f : ℝ⟦X⟧) (hf : constantCoeff f = 1) :
    cumulant f 4 = moment f 4 - 4 * moment f 3 * moment f 1 - 3 * moment f 2 ^ 2 +
      12 * moment f 2 * moment f 1 ^ 2 - 6 * moment f 1 ^ 4 := by
  have h := recurrence f hf 3
  norm_num [sum_range_succ, cumulant_one f hf, cumulant_two f hf, cumulant_three f hf] at h
  rw [h]
  ring

end PaperP1.FormalFactorialCumulants
