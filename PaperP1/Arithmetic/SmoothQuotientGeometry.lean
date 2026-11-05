module

public import PaperP1.Arithmetic.SmoothRecursiveLower

/-! # Refined integer quotient geometry for smooth-count induction

Above Y squared the relative quotient loss is at most1/Y, uniformly in
all positive prime candidates p<=Y. Every quotient remains literal.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothQuotientGeometry

theorem quotient_relative_lower {X Y p : ℕ} (hY : 2 ≤ Y) (hp : 0 < p)
    (hpy : p ≤ Y) (hsquare : Y ^ 2 ≤ X) :
    (1 - 1 / (Y : ℝ)) * (X : ℝ) / p ≤ ((X / p : ℕ) : ℝ) := by
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : X % p ≤ Y := (Nat.mod_lt X hp).le.trans hpy
  have hrem : Y * (X % p) ≤ X := (Nat.mul_le_mul_left Y hr).trans (by simpa only [pow_two] using hsquare)
  have hremR : (Y : ℝ) * (X % p : ℕ) ≤ X := by exact_mod_cast hrem
  have hidentity : (X : ℝ) = (X % p : ℕ) + (p : ℝ) * (X / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div X p).symm
  apply (div_le_iff₀ hpr).mpr
  have hid : (1 - 1 / (Y : ℝ)) * (X : ℝ) = (((Y : ℝ) - 1) * X) / Y := by field_simp
  rw [hid]
  apply (div_le_iff₀ hy).mpr
  have heq : ((X / p : ℕ) : ℝ) * p * Y - ((Y : ℝ) - 1) * X = (X : ℝ) - (Y : ℝ) * (X % p : ℕ) := by
    rw [hidentity]
    ring
  nlinarith only [heq, hremR]

theorem log_quotient_upper {X Y p : ℕ} (hY : 2 ≤ Y) (hp : 0 < p) (hpx : p ≤ X) :
    Real.log ((X / p : ℕ) : ℝ) / Real.log Y ≤ Real.log X / Real.log Y - Real.log p / Real.log Y := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hp.trans_le hpx
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : (0 : ℝ) < ((X / p : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hpx hp
  have hl := Real.log_le_log hq (Nat.cast_div_le : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / p)
  rw [Real.log_div hx.ne' hpr.ne'] at hl
  have hy : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  simpa only [sub_div] using div_le_div_of_nonneg_right hl (Real.log_pos hy).le

theorem square_le_of_ratio {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hratio : 2 ≤ Real.log X / Real.log Y) : Y ^ 2 ≤ X := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hy : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hl := (le_div_iff₀ (Real.log_pos hy)).mp hratio
  have hlog : Real.log ((Y : ℝ) ^ 2) ≤ Real.log X := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hl
  have hh := (Real.log_le_log_iff (pow_pos (by linarith only [hy] : (0 : ℝ) < Y) 2) hx).mp hlog
  exact_mod_cast hh

end PaperP1.SmoothQuotientGeometry
