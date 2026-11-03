module

public import PaperP1.Algebra.FourthCharlierPolynomial
public import PaperP1.Probability.PoissonFactorialMoments

/-! # The fourth Charlier test vanishes on the exact quadratic signed reference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthCharlierReference

open PaperP1.PoissonSequence PaperP1.PoissonFactorialMoments

theorem second_shift_factorial_succ_succ (μ : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    HasSum (fun k : ℕ ↦ shift (shift (mass μ)) k * (k.descFactorial (j + 2) : ℝ))
      (μ ^ (j + 2) + 2 * (j + 2 : ℝ) * μ ^ (j + 1) +
        (j + 2 : ℝ) * (j + 1 : ℝ) * μ ^ j) := by
  apply hasSum_shift_weighted
  have h := (hasSum_shift_mass_factorial_succ μ hμ (j + 1)).add
    ((hasSum_shift_mass_factorial_succ μ hμ j).mul_left (j + 2 : ℝ))
  convert h using 1
  · funext k
    rw [show j + 2 = (j + 1) + 1 by omega, descFactorial_succ_add]
    push_cast
    ring
  · push_cast
    ring

theorem quadratic_factorial_succ_succ (μ α : ℝ) (hμ : 0 ≤ μ) (j : ℕ) :
    HasSum (fun k : ℕ ↦ quadraticMass μ α k * (k.descFactorial (j + 2) : ℝ))
      (μ ^ (j + 2) + α * ((j + 2 : ℝ) * (j + 1 : ℝ) / 2) * μ ^ j) := by
  have hm := hasSum_mass_factorial μ hμ (j + 2)
  have hs := hasSum_shift_mass_factorial_succ μ hμ (j + 1)
  have hss := second_shift_factorial_succ_succ μ hμ j
  have h := hm.add (((hss.sub (hs.mul_left 2)).add hm).mul_left (α / 2))
  convert h using 1
  · funext k
    unfold quadraticMass secondDifference
    ring
  · push_cast
    ring

theorem quadratic_first (μ α : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ ↦ quadraticMass μ α k * (k : ℝ)) μ := by
  have hm : HasSum (fun k : ℕ ↦ mass μ k * (k : ℝ)) μ := by
    simpa only [Nat.descFactorial_one, pow_one] using hasSum_mass_factorial μ hμ 1
  have hs : HasSum (fun k : ℕ ↦ shift (mass μ) k * (k : ℝ)) (μ + 1) := by
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add, Nat.descFactorial_one, one_mul, pow_one, pow_zero] using
      hasSum_shift_mass_factorial_succ μ hμ 0
  have hss : HasSum (fun k : ℕ ↦ shift (shift (mass μ)) k * (k : ℝ)) (μ + 2) := by
    apply hasSum_shift_weighted
    have h := hs.add (hasSum_shift (hasSum_mass μ hμ))
    convert h using 1
    · funext k; push_cast; ring
    · ring
  have h := hm.add (((hss.sub (hs.mul_left 2)).add hm).mul_left (α / 2))
  convert h using 1
  · funext k; unfold quadraticMass secondDifference; ring
  · ring

theorem hasSum_zero (μ α : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ ↦ quadraticMass μ α k * FourthCharlierPolynomial.value μ k) 0 := by
  have h4 := quadratic_factorial_succ_succ μ α hμ 2
  have h3 := quadratic_factorial_succ_succ μ α hμ 1
  have h2 := quadratic_factorial_succ_succ μ α hμ 0
  have h1 := quadratic_first μ α hμ
  have h0 := hasSum_quadraticMass μ α hμ
  have h := (((h4.sub (h3.mul_left (4 * μ))).add (h2.mul_left (6 * μ ^ 2))).sub
    (h1.mul_left (4 * μ ^ 3))).add (h0.mul_left (μ ^ 4))
  convert h using 1
  · funext k; unfold FourthCharlierPolynomial.value; ring
  · norm_num; ring

end PaperP1.FourthCharlierReference
