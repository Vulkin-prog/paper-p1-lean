module

public import PaperP1.Probability.PoissonExponential
public import Mathlib.Data.Nat.Choose.Cast

/-! # Closed factorial-moment sums for the Poisson mass sequence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonFactorialMoments

open PaperP1.PoissonSequence Finset

theorem mass_add_mul_descFactorial (μ : ℝ) (n j : ℕ) :
    mass μ (n + j) * ((n + j).descFactorial j : ℝ) = μ ^ j * mass μ n := by
  have hf := Nat.factorial_mul_descFactorial (show j ≤ n + j by omega)
  rw [Nat.add_sub_cancel_right] at hf
  have hfr : (n.factorial : ℝ) * ((n + j).descFactorial j : ℝ) = ((n + j).factorial : ℝ) := by
    exact_mod_cast hf
  have hdNat : (n + j).descFactorial j ≠ 0 := by
    intro hz
    have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hz
    omega
  have hd : ((n + j).descFactorial j : ℝ) ≠ 0 := by exact_mod_cast hdNat
  unfold mass
  rw [pow_add, ← hfr]
  field_simp

theorem hasSum_mass_factorial (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    HasSum (fun k : ℕ ↦ mass μ k * (k.descFactorial j : ℝ)) (μ ^ j) := by
  have ht : HasSum (fun n : ℕ ↦ mass μ (n + j) * ((n + j).descFactorial j : ℝ)) (μ ^ j) := by
    simpa only [mass_add_mul_descFactorial, mul_one] using (hasSum_mass μ hμ).mul_left (μ ^ j)
  have h := (hasSum_nat_add_iff (f := fun k : ℕ ↦ mass μ k * (k.descFactorial j : ℝ)) j).mp ht
  have hz : (∑ k ∈ range j, mass μ k * (k.descFactorial j : ℝ)) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [Nat.descFactorial_of_lt (mem_range.mp hk), Nat.cast_zero, mul_zero]
  simpa only [hz, add_zero] using h

theorem descFactorial_succ_add (k j : ℕ) :
    (k + 1).descFactorial (j + 1) =
      k.descFactorial (j + 1) + (j + 1) * k.descFactorial j := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_succ_succ', Nat.factorial_succ]
  ring

theorem hasSum_shift_weighted {a : ℕ → ℝ} (f : ℕ → ℝ) {s : ℝ}
    (ha : HasSum (fun k : ℕ ↦ a k * f (k + 1)) s) :
    HasSum (fun k : ℕ ↦ shift a k * f k) s := by
  have h := hasSum_shift ha
  convert h using 1
  funext k
  cases k <;> simp

theorem hasSum_shift_mass_factorial_succ (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    HasSum (fun k : ℕ ↦ shift (mass μ) k * (k.descFactorial (j + 1) : ℝ))
      (μ ^ (j + 1) + (j + 1 : ℝ) * μ ^ j) := by
  apply hasSum_shift_weighted
  have h := (hasSum_mass_factorial μ hμ (j + 1)).add
    ((hasSum_mass_factorial μ hμ j).mul_left (j + 1 : ℝ))
  convert h using 1
  funext k
  rw [descFactorial_succ_add]
  push_cast
  ring

theorem hasSum_shift_mass_factorial_zero (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ ↦ shift (mass μ) k * (k.descFactorial 0 : ℝ)) 1 := by
  simpa only [Nat.descFactorial_zero, Nat.cast_one, mul_one] using hasSum_shift (hasSum_mass μ hμ)

theorem hasSum_shift_one_factorial (j : ℕ) :
    HasSum (fun k : ℕ ↦ shift (mass 1) k * (k.descFactorial j : ℝ)) (1 + j : ℝ) := by
  cases j with
  | zero => simpa using hasSum_shift_mass_factorial_zero 1 (by norm_num)
  | succ j =>
    simpa only [one_pow, Nat.cast_add, Nat.cast_one, mul_one] using
      hasSum_shift_mass_factorial_succ 1 (by norm_num) j

theorem hasSum_second_shift_one_factorial (j : ℕ) :
    HasSum (fun k : ℕ ↦ shift (shift (mass 1)) k * (k.descFactorial j : ℝ))
      (1 + 2 * j + (j : ℝ) * ((j : ℝ) - 1)) := by
  cases j with
  | zero =>
    simpa only [Nat.descFactorial_zero, Nat.cast_zero, Nat.cast_one, mul_one, mul_zero,
      zero_mul, add_zero] using hasSum_shift (hasSum_shift (hasSum_mass 1 (by norm_num)))
  | succ j =>
    apply hasSum_shift_weighted
    have h := (hasSum_shift_one_factorial (j + 1)).add
      ((hasSum_shift_one_factorial j).mul_left (j + 1 : ℝ))
    convert h using 1
    · funext k
      rw [descFactorial_succ_add]
      push_cast
      ring
    · push_cast
      ring

theorem hasSum_quadratic_one_factorial (a : ℝ) (j : ℕ) :
    HasSum (fun k : ℕ ↦ quadraticMass 1 a k * (k.descFactorial j : ℝ))
      (1 + a * (j.choose 2 : ℝ)) := by
  have hm : HasSum (fun k : ℕ ↦ mass 1 k * (k.descFactorial j : ℝ)) 1 := by
    simpa only [one_pow] using hasSum_mass_factorial 1 (by norm_num) j
  have hs := hasSum_shift_one_factorial j
  have hss := hasSum_second_shift_one_factorial j
  have h := hm.add (((hss.sub (hs.mul_left 2)).add hm).mul_left (a / 2))
  convert h using 1
  · funext k
    unfold quadraticMass secondDifference
    ring
  · rw [Nat.cast_choose_two]
    ring

end PaperP1.PoissonFactorialMoments
