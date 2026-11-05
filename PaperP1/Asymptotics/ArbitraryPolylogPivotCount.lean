module

public import PaperP1.Asymptotics.PolylogPivotCount

/-! # Rankin pivot counts at every fixed logarithmic cutoff power -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ArbitraryPolylogPivotCount

open OddPrimePivot PolylogPivotExceptions

def exponent (m : ℕ) : ℝ := 1 - 1 / (2 * (m : ℝ))

def growthConstant (m : ℕ) : ℝ := (3 : ℝ) ^ exponent m / (1 - exponent m)

def growthFactor (m N : ℕ) : ℝ :=
  growthConstant m * Real.exp ((2 * (m : ℝ)) * Real.sqrt (Real.log N))

theorem exponent_bounds (m : ℕ) (hm : 1 ≤ m) : 1 / 2 ≤ exponent m ∧ exponent m < 1 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < 2 * m := by positivity
  have hi : 1 / (2 * (m : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hmR])
  have hpos : 0 < 1 / (2 * (m : ℝ)) := by positivity
  dsimp only [exponent]
  constructor <;> linarith only [hi, hpos]

theorem log_power_identity (m : ℕ) (hm : 1 ≤ m) {z : ℝ} (hz : 0 ≤ z) :
    (z ^ m) ^ (1 - exponent m) = Real.sqrt z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz, Real.sqrt_eq_rpow]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  dsimp only [exponent]
  field_simp
  ring

theorem finite_value_bound (m : ℕ) (hm : 1 ≤ m) {N Y : ℕ} (hN : 2 ≤ N) (hY : 1 ≤ Y)
    (hcut : (Y : ℝ) ≤ (Real.log N) ^ m) :
    ((pivotValues (3 * N) Y).card : ℝ) ≤ growthFactor m N * (N : ℝ) ^ exponent m := by
  obtain ⟨hσ, hσ1⟩ := exponent_bounds m hm
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog := Real.log_nonneg hn1
  have hy := Real.rpow_le_rpow (Nat.cast_nonneg Y) hcut (by linarith only [hσ1] : 0 ≤ 1 - exponent m)
  rw [log_power_identity m hm hlog] at hy
  have hb := pivot_count_rankin (3 * N) Y hY (exponent m) hσ hσ1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hi : 1 / (1 - exponent m) = 2 * (m : ℝ) := by
    dsimp only [exponent]
    field_simp
    ring
  have he : Real.exp ((Y : ℝ) ^ (1 - exponent m) / (1 - exponent m)) ≤
      Real.exp ((2 * (m : ℝ)) * Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, ← one_div, hi]
    nlinarith only [hy, hmpos]
  calc
    _ ≤ ((3 * N : ℕ) : ℝ) ^ exponent m * (1 / (1 - exponent m)) *
        Real.exp ((Y : ℝ) ^ (1 - exponent m) / (1 - exponent m)) := hb
    _ ≤ ((3 * N : ℕ) : ℝ) ^ exponent m * (1 / (1 - exponent m)) *
        Real.exp ((2 * (m : ℝ)) * Real.sqrt (Real.log N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = growthFactor m N * (N : ℝ) ^ exponent m := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg N)]
      unfold growthFactor growthConstant
      ring

theorem uniform_growth (m : ℕ) (admissible : ℕ → ℕ → Prop) :
    UniformSubpolynomialOn admissible (fun N _ ↦ growthFactor m N) :=
  ExpSqrtLog.uniformSubpolynomialOn_const_mul (growthConstant m)
    (ExpSqrtLog.uniformSubpolynomialOn admissible (2 * m) (by positivity))

theorem uniform_value_bound (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Y : ℕ, 1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ m →
      ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) ^ (exponent m + ε) := by
  obtain ⟨NF, hf⟩ := UniformSubpolynomialPower.bound (uniform_growth m (fun _ _ ↦ True)) ε hε
  refine ⟨max NF 2, by omega, ?_⟩
  intro N hN Y hY hcut
  have hh := hf N (by omega) 0 trivial
  have hg : 0 ≤ growthFactor m N := by
    unfold growthFactor growthConstant
    have hσ1 := (exponent_bounds m hm).2
    positivity
  rw [abs_of_nonneg hg] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ growthFactor m N * (N : ℝ) ^ exponent m := finite_value_bound m hm (by omega) hY hcut
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ exponent m :=
      mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ArbitraryPolylogPivotCount
