module

public import PaperP1.Arithmetic.QuadraticDegreeUniformFieldCount
public import PaperP1.Arithmetic.LinearHeightShearBudget

/-! # The polynomial-in-degree integer projection height loses only a dimension-dependent factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveProjectionHeightBudget

open DegreeUniformAffineParameters QuadraticDegreeUniformFieldCount

def coefficient (n d : ℕ) : ℕ := ((n - 1) * d ^ 2 + 1) ^ (n - 1)

def rootFactor (n : ℕ) : ℕ := n ^ n * 2 ^ (2 * (n - 1))

def heightExponent (n : ℕ) : ℕ := n ^ n + n * (2 * (n - 1)) + 1

def profileFactor (n : ℕ) : ℕ := rootFactor n * heightExponent n ^ 17

theorem coefficient_pos (n d : ℕ) : 0 < coefficient n d := by
  unfold coefficient
  positivity

theorem rootFactor_pos (n : ℕ) (hn : 0 < n) : 0 < rootFactor n := by
  unfold rootFactor
  positivity

theorem heightExponent_pos (n : ℕ) : 0 < heightExponent n := by
  unfold heightExponent
  omega

theorem profileFactor_pos (n : ℕ) (hn : 0 < n) : 0 < profileFactor n :=
  Nat.mul_pos (rootFactor_pos n hn) (pow_pos (heightExponent_pos n) 17)

theorem coefficient_polynomial (n d : ℕ) (hn : 1 ≤ n) (hd : 0 < d) :
    n * coefficient n d ≤ n ^ n * d ^ (2 * (n - 1)) := by
  have hd2 : 1 ≤ d ^ 2 := one_le_pow₀ (by omega)
  have hbase : (n - 1) * d ^ 2 + 1 ≤ n * d ^ 2 := by
    have he : n = (n - 1) + 1 := by omega
    rw [he] at ⊢
    have hh : (n - 1 + 1 - 1) = n - 1 := by omega
    rw [hh]
    nlinarith only [hd2]
  calc
    _ ≤ n * (n * d ^ 2) ^ (n - 1) :=
      Nat.mul_le_mul_left n (Nat.pow_le_pow_left hbase (n - 1))
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]

theorem coefficient_exponential (n d : ℕ) (hn : 1 ≤ n) (hd : 0 < d) :
    n * coefficient n d ≤ rootFactor n ^ d := by
  calc
    _ ≤ n ^ n * d ^ (2 * (n - 1)) := coefficient_polynomial n d hn hd
    _ ≤ (n ^ n) ^ d * (2 ^ d) ^ (2 * (n - 1)) :=
      Nat.mul_le_mul (Nat.le_self_pow hd.ne' _) (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = _ := by
      rw [rootFactor, mul_pow]
      congr 1
      rw [← pow_mul, ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _

theorem height_power_bound (n d H : ℕ) (hn : 1 ≤ n) (hd : 0 < d) (hH : 2 ≤ H)
    (hcap : d ≤ H ^ n) : n * coefficient n d * H ≤ H ^ heightExponent n := by
  have hA : n ^ n ≤ H ^ (n ^ n) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hH _)
  calc
    _ ≤ n ^ n * d ^ (2 * (n - 1)) * H :=
      Nat.mul_le_mul_right H (coefficient_polynomial n d hn hd)
    _ ≤ H ^ (n ^ n) * (H ^ n) ^ (2 * (n - 1)) * H :=
      Nat.mul_le_mul_right H (Nat.mul_le_mul hA (Nat.pow_le_pow_left hcap _))
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_succ]; rfl

theorem budget_of_le_power (M H m : ℕ) (hM : 0 < M) (hm : 0 < m) (hbound : M ≤ H ^ m) :
    logarithmicBudget M ≤ m * logarithmicBudget H := by
  have hpow : M < 2 ^ (m * logarithmicBudget H) := by
    calc
      _ ≤ H ^ m := hbound
      _ < (2 ^ logarithmicBudget H) ^ m := Nat.pow_lt_pow_left (binary_upper H) hm.ne'
      _ = _ := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hh := Nat.log_lt_of_lt_pow hM.ne' hpow
  simp only [logarithmicBudget, Nat.log2_eq_log_two] at *
  omega

theorem logarithmic_bound (n d H : ℕ) (hn : 1 ≤ n) (hd : 0 < d) (hH : 2 ≤ H)
    (hcap : d ≤ H ^ n) :
    logarithmicBudget (n * coefficient n d * H) ≤ heightExponent n * logarithmicBudget H := by
  apply budget_of_le_power
  · exact Nat.mul_pos (Nat.mul_pos (by omega) (coefficient_pos n d)) (by omega)
  · exact heightExponent_pos n
  · exact height_power_bound n d H hn hd hH hcap

theorem root_bound (n d H : ℕ) (hn : 1 ≤ n) (hd : 0 < d) :
    ((n * coefficient n d * H : ℕ) : ℝ) ^ (1 / (d : ℝ)) ≤
      (rootFactor n : ℝ) * (H : ℝ) ^ (1 / (d : ℝ)) := by
  have hbound : ((n * coefficient n d * H : ℕ) : ℝ) ≤ (rootFactor n : ℝ) ^ d * (H : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right H (coefficient_exponential n d hn hd)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ ((rootFactor n : ℝ) ^ d * (H : ℝ)) ^ (1 / (d : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbound (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hd0, Real.rpow_one]

theorem profile_bound (n d H : ℕ) (hn : 1 ≤ n) (hd : 0 < d) (hH : 2 ≤ H)
    (hcap : d ≤ H ^ n) :
    profile d (n * coefficient n d * H) ≤ (profileFactor n : ℝ) * profile d H := by
  have hlog : (logarithmicBudget (n * coefficient n d * H) : ℝ) ≤
      (heightExponent n : ℝ) * (logarithmicBudget H : ℝ) := by
    exact_mod_cast logarithmic_bound n d H hn hd hH hcap
  have hlogpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hlog 17
  rw [mul_pow] at hlogpow
  have hroot := root_bound n d H hn hd
  calc
    _ ≤ (d : ℝ) ^ 2 * ((heightExponent n : ℝ) ^ 17 * (logarithmicBudget H : ℝ) ^ 17) *
        ((rootFactor n : ℝ) * (H : ℝ) ^ (1 / (d : ℝ))) := by
      unfold profile
      gcongr
    _ = _ := by
      simp only [profile, profileFactor, Nat.cast_mul, Nat.cast_pow]
      ring

end PaperP1.CurveProjectionHeightBudget
