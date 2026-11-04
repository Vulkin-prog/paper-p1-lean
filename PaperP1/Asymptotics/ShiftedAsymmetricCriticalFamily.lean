module

public import PaperP1.Arithmetic.ShiftedAsymmetricPopulation
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # The shifted asymmetric population on an actual critical sequence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedAsymmetricCriticalFamily

open PaperP1.AsymmetricShiftedWitness PaperP1.ShiftedAsymmetricPopulation

def scale (k : ℕ) : ℕ := 2 ^ (3 * k)

def dyadicScale (k : ℕ) : ℕ := 6 * scale k

theorem scale_pos (k : ℕ) : 0 < scale k := by unfold scale; positivity

theorem index_le_scale (k : ℕ) : k ≤ scale k := by
  induction k with
  | zero => norm_num [scale]
  | succ k ih =>
    have hp := scale_pos k
    have he : scale (k + 1) = scale k * 8 := by
      simp only [scale, show 3 * (k + 1) = 3 * k + 3 by omega, pow_add]
      norm_num
    rw [he]
    omega

theorem critical_band (k : ℕ) :
    |((3 * k : ℕ) : ℝ) - Real.log (dyadicScale k) / Real.log 2| ≤ 3 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hupper : Real.log 6 ≤ 3 * Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 6)
      (by norm_num : (6 : ℝ) ≤ 2 ^ (3 : ℕ))
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlog : Real.log (dyadicScale k) = Real.log 6 + (3 * k : ℕ) * Real.log 2 := by
    simp only [dyadicScale, scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity), Real.log_pow]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have he : ((3 * k : ℕ) : ℝ) - Real.log (dyadicScale k) / Real.log 2 =
      -(Real.log 6 / Real.log 2) := by
    rw [hlog]
    field_simp
    ring
  rw [he, abs_neg, abs_of_nonneg (div_nonneg h6 h2.le)]
  exact (div_le_iff₀ h2).mpr hupper

theorem width_constraints :
    ∃ K : ℕ, ∀ k ≥ K, 2 * width k ≤ scale k ∧ 5 * (width k) ^ 4 < 3 * scale k := by
  obtain ⟨N₀, hN₀⟩ := CriticalPolynomialScale.polynomial_lt_scale 3 24 (by norm_num) 4
  refine ⟨N₀, ?_⟩
  intro k hk
  have hN : N₀ ≤ dyadicScale k := by
    have hi := index_le_scale k
    dsimp [dyadicScale]
    omega
  have hh := hN₀ (dyadicScale k) hN (3 * k) (critical_band k)
  have hn : 24 * (width k) ^ 4 < 6 * scale k := by
    exact_mod_cast hh
  have hB : 1 ≤ width k := by dsimp [width]; omega
  have hp : width k ≤ (width k) ^ 4 := le_self_pow₀ hB (by decide)
  constructor <;> omega

theorem scale_four_thirds (k : ℕ) : (scale k : ℝ) ^ (4 / 3 : ℝ) = (2 : ℝ) ^ (4 * k) := by
  simp only [scale, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ((3 * k : ℕ) : ℝ) * (4 / 3 : ℝ) = ((4 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem exponential_lower (k : ℕ) (hk : 2 ≤ k) :
    (2 : ℝ) ^ (k - 2) ≤ (2 : ℝ) ^ (k - 1) - 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ (k - 2) := one_le_pow₀ (by norm_num)
  rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  linarith

theorem total_lower_four_thirds {H : ℕ} (hH : 3 ≤ H) (k : ℕ) (hk : 2 ≤ k)
    (hwidth : 2 * width k ≤ scale k) (hlarge : 5 * (width k) ^ 4 < 3 * scale k) :
    (scale k : ℝ) ^ (4 / 3 : ℝ) / 8 ≤ total (dyadicScale k) H k := by
  have hB : width k ≤ scale k := by omega
  have hhalf : (scale k : ℝ) / 2 ≤ (scale k : ℝ) - width k := by
    have hh : (2 : ℝ) * width k ≤ scale k := by exact_mod_cast hwidth
    linarith
  have hpow : (2 : ℝ) ^ (3 * k) * 2 ^ (k - 2) * 4 = (2 : ℝ) ^ (4 * k) := by
    rw [← pow_add, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_add]
    congr 1
    omega
  calc
    _ = (scale k : ℝ) / 2 * (2 : ℝ) ^ (k - 2) := by
      rw [scale_four_thirds]
      simp only [scale, Nat.cast_pow, Nat.cast_ofNat]
      linarith only [hpow]
    _ ≤ ((scale k : ℝ) - width k) * ((2 : ℝ) ^ (k - 1) - 1) :=
      mul_le_mul hhalf (exponential_lower k hk) (by positivity) (by linarith)
    _ ≤ _ := total_lower hH (scale k) k hB hlarge

end PaperP1.ShiftedAsymmetricCriticalFamily
