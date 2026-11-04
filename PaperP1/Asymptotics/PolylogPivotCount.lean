module

public import PaperP1.Arithmetic.PolylogPivotExceptions
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformSubpolynomialPower

/-! # The actual log-fifth pivot exclusions are uniformly N^(9/10+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogPivotCount

open PaperP1.OddPrimePivot PaperP1.PolylogPivotExceptions

def growthConstant : ℝ := 10 * (3 : ℝ) ^ (9 / 10 : ℝ)

def growthFactor (N : ℕ) : ℝ := growthConstant * Real.exp (10 * Real.sqrt (Real.log N))

theorem growthFactor_nonneg (N : ℕ) : 0 ≤ growthFactor N := by
  unfold growthFactor growthConstant
  positivity

theorem log_power_identity {z : ℝ} (hz : 0 ≤ z) :
    (z ^ 5) ^ (1 / 10 : ℝ) = Real.sqrt z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
  norm_num
  rw [← Real.sqrt_eq_rpow]

theorem finite_value_bound {N Y : ℕ} (hN : 2 ≤ N) (hY : 1 ≤ Y)
    (hcut : (Y : ℝ) ≤ (Real.log N) ^ 5) :
    ((pivotValues (3 * N) Y).card : ℝ) ≤ growthFactor N * (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hn
  have hy := Real.rpow_le_rpow (Nat.cast_nonneg Y) hcut (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rw [log_power_identity hlog] at hy
  have hb := pivot_count_rankin (3 * N) Y hY (9 / 10) (by norm_num) (by norm_num)
  norm_num only [show (1 : ℝ) - 9 / 10 = 1 / 10 by norm_num,
    show (1 : ℝ) / (1 / 10) = 10 by norm_num] at hb
  have he : Real.exp ((Y : ℝ) ^ (1 / 10 : ℝ) / (1 / 10)) ≤
      Real.exp (10 * Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hy]
  calc
    _ ≤ ((3 * N : ℕ) : ℝ) ^ (9 / 10 : ℝ) * 10 *
        Real.exp ((Y : ℝ) ^ (1 / 10 : ℝ) / (1 / 10)) := hb
    _ ≤ ((3 * N : ℕ) : ℝ) ^ (9 / 10 : ℝ) * 10 *
        Real.exp (10 * Real.sqrt (Real.log N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = growthFactor N * (N : ℝ) ^ (9 / 10 : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg N)]
      unfold growthFactor growthConstant
      ring

theorem uniform_growth (admissible : ℕ → ℕ → Prop) :
    PaperP1.UniformSubpolynomialOn admissible (fun N _ ↦ growthFactor N) :=
  PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const_mul growthConstant
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn admissible 10 (by norm_num))

theorem uniform_value_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y : ℕ, 1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) ^ (9 / 10 + ε : ℝ) := by
  obtain ⟨NF, hF⟩ := PaperP1.UniformSubpolynomialPower.bound
    (uniform_growth (fun _ _ ↦ True)) ε hε
  refine ⟨max NF 2, ?_⟩
  intro N hN Y hY hcut
  have hf := hF N (by omega) 0 trivial
  rw [abs_of_nonneg (growthFactor_nonneg N)] at hf
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ growthFactor N * (N : ℝ) ^ (9 / 10 : ℝ) := finite_value_bound (by omega) hY hcut
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_window_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B Y : ℕ, (B : ℝ) ≤ D * Real.log N →
      1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      ((badWindows N B Y).card : ℝ) ≤ (N : ℝ) ^ (9 / 10 + ε : ℝ) := by
  have hlin := PaperP1.ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) D hD (fun _ _ h ↦ h)
  have hmul := PaperP1.ExpSqrtLog.uniformSubpolynomialOn_mul hlin
    (uniform_growth (fun N B ↦ (B : ℝ) ≤ D * Real.log N))
  obtain ⟨NF, hF⟩ := PaperP1.UniformSubpolynomialPower.bound hmul ε hε
  obtain ⟨NB, hNB⟩ := PaperP1.ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually D hD 1 (by omega)
  refine ⟨max (max NF NB) 2, ?_⟩
  intro N hN B Y hB hY hcut
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBN : B ≤ N := by
    have hw := hNB N (by omega) B hB
    simp only [pow_one] at hw
    have : (B : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hf := hF N (by omega) B hB
  rw [abs_of_nonneg (mul_nonneg (by positivity) (growthFactor_nonneg N))] at hf
  have hc : ((badWindows N B Y).card : ℝ) ≤ B * (pivotValues (3 * N) Y).card := by
    exact_mod_cast badWindows_card (Y := Y) (by omega) hBN
  calc
    _ ≤ B * (growthFactor N * (N : ℝ) ^ (9 / 10 : ℝ)) :=
      hc.trans (mul_le_mul_of_nonneg_left (finite_value_bound (by omega) hY hcut) (Nat.cast_nonneg B))
    _ ≤ ((B + 1 : ℝ) * growthFactor N) * (N : ℝ) ^ (9 / 10 : ℝ) := by
      have hg := growthFactor_nonneg N
      have hp := Real.rpow_nonneg hn.le (9 / 10 : ℝ)
      nlinarith only [mul_nonneg hg hp]
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.PolylogPivotCount
