module

public import PaperP1.Arithmetic.DegreeUniformAffineParameters

/-! # Logarithmic and root costs of the bounded shear

The enlarged radius `(D+1)N` loses only absolute constants in both factors.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHeightShearBudget

open DegreeUniformAffineParameters

theorem scale_bounds (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N) :
    N ≤ (D + 1) * N ∧ (D + 1) * N ≤ N ^ 3 := by
  exact ⟨by nlinarith only [Nat.zero_le (D * N)], box_le_cubic D N hD hDN⟩

theorem logarithmic_bound (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N) :
    logarithmicBudget ((D + 1) * N) ≤ 3 * logarithmicBudget N := by
  have hN : 0 < N := by omega
  have hpos : (D + 1) * N ≠ 0 := by positivity
  have hpow : (D + 1) * N < 2 ^ (3 * logarithmicBudget N) := by
    calc
      _ ≤ N ^ 3 := (scale_bounds D N hD hDN).2
      _ < (2 ^ logarithmicBudget N) ^ 3 :=
        Nat.pow_lt_pow_left (binary_upper N) (by decide : 3 ≠ 0)
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hh := Nat.log_lt_of_lt_pow hpos hpow
  simp only [logarithmicBudget, Nat.log2_eq_log_two] at *
  omega

theorem root_scale (D N : ℕ) (hD : 1 ≤ D) :
    (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤
      2 * (N : ℝ) ^ (1 / (D : ℝ)) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hpow : ((D + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast (Nat.succ_le_of_lt (show D < 2 ^ D from Nat.lt_two_pow_self))
  have hroot : (((D + 1 : ℕ) : ℝ)) ^ (1 / (D : ℝ)) ≤ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ D) ^ (1 / (D : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [mul_one_div_cancel hd.ne', Real.rpow_one]
  rw [Nat.cast_mul, Real.mul_rpow (by positivity) (Nat.cast_nonneg N)]
  exact mul_le_mul_of_nonneg_right hroot (by positivity)

end PaperP1.LinearHeightShearBudget
