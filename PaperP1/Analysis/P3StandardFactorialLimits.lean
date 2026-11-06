module

public import PaperP1.Analysis.P3StandardMonomialLimits
public import PaperP1.Arithmetic.SmallPrimeBudget
public import Mathlib.Data.Nat.Choose.Bounds

/-! # The actual standard-family factorial is negligible on the global surface cubic scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardFactorialLimits

open Filter Topology P3StandardMonomialParameters

theorem size_le_cube (d e : ℕ) : size d e ≤ (e + 3) ^ 3 :=
  (Nat.sub_le _ _).trans (Nat.choose_le_pow (e + 3) 3)

theorem factorial_log_bound (d e : ℕ) (he : 1 ≤ e) :
    Real.log ((size d e).factorial : ℝ) ≤
      (size d e : ℝ) * (3 * Real.log 4 + 3 * Real.log (e : ℝ)) := by
  by_cases hs : size d e = 0
  · simp only [hs, Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul, le_refl]
  · have hspos : (0 : ℝ) < size d e := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hsR : (size d e : ℝ) ≤ ((e : ℝ) + 3) ^ 3 := by exact_mod_cast size_le_cube d e
    have hlog := Real.log_le_log hspos hsR
    rw [Real.log_pow] at hlog
    change Real.log (size d e : ℝ) ≤ 3 * Real.log ((e : ℝ) + 3) at hlog
    have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hepos : (0 : ℝ) < e := by linarith
    have hh := Real.log_le_log (show 0 < (e : ℝ) + 3 by positivity)
      (show (e : ℝ) + 3 ≤ 4 * (e : ℝ) by linarith)
    rw [Real.log_mul (by norm_num) hepos.ne'] at hh
    have ht : Real.log (size d e : ℝ) ≤ 3 * Real.log 4 + 3 * Real.log (e : ℝ) := by linarith
    exact (SmallPrimeBudget.log_factorial_le (size d e)).trans
      (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

theorem factorial_cubic_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ Real.log ((size d e).factorial : ℝ) / (e : ℝ) ^ 3) atTop (𝓝 0) := by
  have hi : Tendsto (fun e : ℕ ↦ (e : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun e : ℕ ↦ Real.log (e : ℝ) / (e : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hb := (P3StandardMonomialLimits.size_ratio d).mul
    ((hi.const_mul (3 * Real.log 4)).add (hl.const_mul 3))
  simp only [mul_zero, zero_add] at hb
  have hn : ∀ᶠ e : ℕ in atTop, 0 ≤ Real.log ((size d e).factorial : ℝ) / (e : ℝ) ^ 3 :=
    Filter.Eventually.of_forall (fun e ↦ div_nonneg (Real.log_natCast_nonneg _) (pow_nonneg (Nat.cast_nonneg e) 3))
  have hu : ∀ᶠ e : ℕ in atTop, Real.log ((size d e).factorial : ℝ) / (e : ℝ) ^ 3 ≤
      ((size d e : ℝ) / (e : ℝ) ^ 2) *
        ((3 * Real.log 4) * (e : ℝ)⁻¹ + 3 * (Real.log (e : ℝ) / (e : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    calc
      _ ≤ (size d e : ℝ) * (3 * Real.log 4 + 3 * Real.log (e : ℝ)) / (e : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (factorial_log_bound d e he) (pow_nonneg (Nat.cast_nonneg e) 3)
      _ = _ := by field_simp [he0]
  exact squeeze_zero' hn hu hb

theorem factorial_logarithmic_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ Real.log ((size d e).factorial : ℝ) /
      ((e : ℝ) ^ 3 * Real.log (e : ℝ))) atTop (𝓝 0) := by
  have hi : Tendsto (fun e : ℕ ↦ (Real.log (e : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (factorial_cubic_ratio d).mul hi
  simp only [mul_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun e ↦ by
    change (Real.log ((size d e).factorial : ℝ) / (e : ℝ) ^ 3) * (Real.log (e : ℝ))⁻¹ = _
    simp only [div_eq_mul_inv, mul_inv, mul_assoc])

end PaperP1.P3StandardFactorialLimits
