module

public import PaperP1.Analysis.BanachPowerPerturbation
public import PaperP1.Analysis.BanachExponentialRemainder

/-! # A logarithm-free quadratic approximation to a finite Bernoulli product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BernoulliExponentialApproximation

open PaperP1.BanachPowerPerturbation PaperP1.BanachExponentialRemainder

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

theorem norm_quadratic_error (v : A) (n : ℕ) :
    ‖(1 + v) ^ n - (NormedSpace.exp v) ^ n +
      n • ((1 / 2 : ℝ) • (v ^ 2 * (NormedSpace.exp v) ^ n))‖ ≤
        (2 * (n : ℝ) * ‖v‖ ^ 3 + (n : ℝ) ^ 2 * ‖v‖ ^ 4) *
          Real.exp (((n : ℝ) + 2) * ‖v‖) := by
  cases n with
  | zero => simp
  | succ n =>
    let d := NormedSpace.exp v
    let M := Real.exp ‖v‖
    let q := (1 / 2 : ℝ) • v ^ 2
    have hM : 1 ≤ M := Real.one_le_exp (norm_nonneg v)
    have hM0 : 0 ≤ M := hM.trans' (by norm_num)
    have hx : ‖1 + v‖ ≤ M := by
      calc
        _ ≤ 1 + ‖v‖ := by simpa only [norm_one] using norm_add_le (1 : A) v
        _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp ‖v‖
    have hd : ‖d‖ ≤ M := norm_exp_le v
    have he : ‖1 + v - d‖ ≤ ‖v‖ ^ 2 * M := by
      rw [norm_sub_rev]
      exact norm_exp_sub_linear_le v
    have hq : ‖q‖ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
      dsimp only [q]
      rw [norm_smul]
      norm_num
      exact norm_pow_le v 2
    have hlocal : ‖1 + v - d + q‖ ≤ ‖v‖ ^ 3 * M := by
      have hid : 1 + v - d + q = -(d - (1 + v + q)) := by abel
      rw [hid, norm_neg]
      exact norm_exp_sub_quadratic_le v
    have hd1 : ‖d - 1‖ ≤ ‖v‖ * M := norm_exp_sub_one_le v
    have h := norm_corrected_power_le (1 + v) d q M hM hx hd n
    have hinc : M ^ (n + 1) ≤ M ^ (n + 3) := pow_le_pow_right₀ hM (by omega)
    have hbound :
        ((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * ‖1 + v - d‖ ^ 2 +
          ((n + 1 : ℕ) : ℝ) * (‖1 + v - d + q‖ + ‖q‖ * ‖d - 1‖) * M ^ n ≤
        (2 * ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 3 + ((n + 1 : ℕ) : ℝ) ^ 2 * ‖v‖ ^ 4) *
          M ^ (n + 3) := by
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * (‖v‖ ^ 2 * M) ^ 2 +
            ((n + 1 : ℕ) : ℝ) * (‖v‖ ^ 3 * M +
              ((1 / 2 : ℝ) * ‖v‖ ^ 2) * (‖v‖ * M)) * M ^ n := by gcongr
        _ = ((n + 1 : ℕ) : ℝ) ^ 2 * ‖v‖ ^ 4 * M ^ (n + 3) +
            (3 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 3 * M ^ (n + 1) := by
          simp only [pow_succ]
          ring
        _ ≤ _ := by
          have hi := mul_le_mul_of_nonneg_left hinc
            (by positivity : 0 ≤ (3 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 3)
          have hp : 0 ≤ ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 3 * M ^ (n + 3) := by positivity
          nlinarith only [hi, hp]
    have hfinal := h.trans hbound
    have hexp : M ^ (n + 3) = Real.exp ((((n + 1 : ℕ) : ℝ) + 2) * ‖v‖) := by
      dsimp only [M]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp] at hfinal
    simpa only [q, smul_mul_assoc, d] using hfinal

end PaperP1.BernoulliExponentialApproximation
