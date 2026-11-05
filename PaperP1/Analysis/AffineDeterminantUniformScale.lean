module

public import PaperP1.Analysis.AffineDeterminantDegreeChoice

/-! # A degree-uniform prime scale for the exact affine determinant

The factorial is paid for by 2 to the triangular determinant valuation.
The auxiliary degree need only dominate the logarithm of the point height.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineDeterminantUniformScale

open AffineMonomialDeterminant

theorem triangle_succ (n : ℕ) :
    (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  have h₀ : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' n.even_mul_pred_self.two_dvd
  have h₁ : 2 * ((n + 1) * n / 2) = (n + 1) * n := by
    simpa only [Nat.add_sub_cancel] using
      Nat.mul_div_cancel' (n + 1).even_mul_pred_self.two_dvd
  have he : n * (n - 1) + 2 * n = (n + 1) * n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  omega

theorem factorial_le_triangle_pow (n : ℕ) : n.factorial ≤ 2 ^ (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
    rw [Nat.factorial_succ]
    have he : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
      simpa only [Nat.add_sub_cancel] using triangle_succ n
    rw [he, pow_add]
    calc
      (n + 1) * n.factorial ≤ 2 ^ n * 2 ^ (n * (n - 1) / 2) := Nat.mul_le_mul hn ih
      _ = _ := by ring

theorem weight_budget (A b : ℕ) (hA : 1 ≤ A) (hb : 2 ≤ b) :
    let J := b - 1
    let k := (A + 1) * (J + 1)
    let v := k * (k - 1) / 2
    1 ≤ v ∧ (weightSum A J : ℝ) ≤ (1 / (b : ℝ) + 1 / ((A : ℝ) + 1)) * v := by
  let J := b - 1
  let k := (A + 1) * (J + 1)
  let v := k * (k - 1) / 2
  change 1 ≤ v ∧ (weightSum A J : ℝ) ≤ (1 / (b : ℝ) + 1 / ((A : ℝ) + 1)) * v
  have hJ : J + 1 = b := by dsimp only [J]; omega
  have hk : k = (A + 1) * b := by dsimp only [k]; rw [hJ]
  have hkfour : 4 ≤ k := by rw [hk]; nlinarith
  obtain ⟨hv, htwov⟩ := LocalDeterminantDegreeChoice.triangle_weight k (by omega)
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  have hAp : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hkR : (k : ℝ) = ((A : ℝ) + 1) * b := by rw [hk]; push_cast; rfl
  have hJR : (J : ℝ) = (b : ℝ) - 1 := by dsimp only [J]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hfrac : 1 / (b : ℝ) + 1 / ((A : ℝ) + 1) =
      ((A : ℝ) + 1 + b) / ((b : ℝ) * ((A : ℝ) + 1)) := by field_simp
  have he : (A : ℝ) + J ≤ (1 / (b : ℝ) + 1 / ((A : ℝ) + 1)) * ((k : ℝ) - 1) := by
    rw [hfrac, div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos hbp hAp)).mpr
    rw [hkR, hJR]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A - 1) (by linarith : (0 : ℝ) ≤ b - 2)]
  have htwow : (2 : ℝ) * (weightSum A J : ℝ) = (k : ℝ) * ((A : ℝ) + J) := by
    have hh := weight_sum_twice A J
    change 2 * weightSum A J = k * (A + J) at hh
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) k)
  refine ⟨hv, ?_⟩
  have hh : (2 : ℝ) * (weightSum A J : ℝ) ≤
      (1 / (b : ℝ) + 1 / ((A : ℝ) + 1)) * (2 * (v : ℝ)) := by
    rw [htwov, htwow]
    nlinarith
  nlinarith

theorem logarithmic_power_bound (H : ℝ) (hH : 1 ≤ H) (A : ℕ)
    (hlog : Real.log H ≤ (A : ℝ) + 1) :
    H ^ (1 / ((A : ℝ) + 1)) ≤ Real.exp 1 := by
  have hHp : 0 < H := by linarith
  have hAp : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos hHp]
  apply Real.exp_le_exp.mpr
  have hh : Real.log H / ((A : ℝ) + 1) ≤ 1 := (div_le_one hAp).mpr hlog
  simpa only [div_eq_mul_inv, one_div, one_mul] using hh

theorem prime_scale (A b : ℕ) (hA : 1 ≤ A) (hb : 2 ≤ b) (H P : ℝ) (hH : 1 ≤ H)
    (hlog : Real.log H ≤ (A : ℝ) + 1) (hP : 3 * Real.exp 1 * H ^ (1 / (b : ℝ)) ≤ P) :
    let J := b - 1
    let k := (A + 1) * (J + 1)
    let v := k * (k - 1) / 2
    (k.factorial : ℝ) * H ^ weightSum A J < P ^ v := by
  let J := b - 1
  let k := (A + 1) * (J + 1)
  let v := k * (k - 1) / 2
  let α := 1 / (b : ℝ) + 1 / ((A : ℝ) + 1)
  change (k.factorial : ℝ) * H ^ weightSum A J < P ^ v
  obtain ⟨hv, hweight⟩ := weight_budget A b hA hb
  have hv' : 1 ≤ v := hv
  have hv0 : v ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hv')
  have hHp : 0 < H := by linarith
  have hfac : (k.factorial : ℝ) ≤ (2 : ℝ) ^ v := by exact_mod_cast factorial_le_triangle_pow k
  have hmon : H ^ weightSum A J ≤ (H ^ α) ^ v := by
    calc
      _ = H ^ (weightSum A J : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ H ^ (α * (v : ℝ)) := Real.rpow_le_rpow_of_exponent_le hH hweight
      _ = _ := Real.rpow_mul_natCast hHp.le α v
  have hbase : H ^ α ≤ Real.exp 1 * H ^ (1 / (b : ℝ)) := by
    dsimp only [α]
    rw [Real.rpow_add hHp]
    calc
      _ ≤ H ^ (1 / (b : ℝ)) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (logarithmic_power_bound H hH A hlog) (Real.rpow_nonneg hHp.le _)
      _ = _ := mul_comm _ _
  have hpos : 0 < Real.exp 1 * H ^ (1 / (b : ℝ)) := by positivity
  calc
    (k.factorial : ℝ) * H ^ weightSum A J ≤ (2 : ℝ) ^ v * (H ^ α) ^ v :=
      mul_le_mul hfac hmon (pow_nonneg hHp.le _) (by positivity)
    _ = (2 * H ^ α) ^ v := (mul_pow _ _ _).symm
    _ ≤ (2 * Real.exp 1 * H ^ (1 / (b : ℝ))) ^ v :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [hbase]) v
    _ < (3 * Real.exp 1 * H ^ (1 / (b : ℝ))) ^ v :=
      pow_lt_pow_left₀ (by nlinarith [hpos]) (by positivity) hv0
    _ ≤ P ^ v := pow_le_pow_left₀ (by positivity) hP v

theorem exists_logarithmic_degree (H : ℝ) (hH : 1 ≤ H) :
    ∃ A : ℕ, 1 ≤ A ∧ Real.log H ≤ (A : ℝ) + 1 ∧ (A : ℝ) ≤ Real.log H + 2 := by
  refine ⟨⌈Real.log H⌉₊ + 1, by omega, ?_, ?_⟩
  · have hh := Nat.le_ceil (Real.log H)
    push_cast
    linarith
  · have hh := Nat.ceil_lt_add_one (Real.log_nonneg hH)
    push_cast
    linarith

end PaperP1.AffineDeterminantUniformScale
