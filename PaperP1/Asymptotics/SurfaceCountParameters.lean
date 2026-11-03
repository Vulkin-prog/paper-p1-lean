module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith

/-! # Fixed degree, equation-count and error choices for the subpower surface-cover argument -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfaceCountParameters

theorem choose_degree (q η : ℝ) (hη : 0 < η) :
    ∃ E : ℕ, 1 ≤ E ∧ q / ((E : ℝ) + 1) ≤ η := by
  obtain ⟨n, hn⟩ := exists_nat_gt (q / η)
  refine ⟨n + 1, by omega, ?_⟩
  have hq : q < (n : ℝ) * η := (div_lt_iff₀ hη).mp hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ) + 1)).mpr
  push_cast
  nlinarith

theorem choose_equations (q η : ℝ) (hη : 0 < η) (kmin : ℕ) :
    ∃ k : ℕ, kmin ≤ k ∧ q / Real.sqrt ((2 : ℝ) ^ k) ≤ η := by
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (q / η) (by norm_num : (1 : ℝ) < 2)
  let m := max t kmin
  have hm : kmin ≤ m := le_max_right t kmin
  have hpow : q / η < (2 : ℝ) ^ m := ht.trans_le
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_left t kmin))
  have hsqrt : Real.sqrt ((2 : ℝ) ^ (2 * m)) = (2 : ℝ) ^ m := by
    rw [Nat.mul_comm 2 m, pow_mul, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  refine ⟨2 * m, by omega, ?_⟩
  rw [hsqrt]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr
  have hq : q < (2 : ℝ) ^ m * η := (div_lt_iff₀ hη).mp hpow
  linarith

theorem subpower_parameters (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 < ε) :
    ∃ (E k : ℕ) (δ : ℝ), 1 ≤ E ∧ 4 * (E + 1) ^ 2 ≤ k ∧ 0 < δ ∧
      2 * q / Real.sqrt ((2 : ℝ) ^ k) + q * δ ≤ ε / 2 ∧
      q / Real.sqrt ((2 : ℝ) ^ k) + q / ((E : ℝ) + 1) + 2 * q * δ ≤ ε / 2 := by
  obtain ⟨E, hE, hdegree⟩ := choose_degree q (ε / 16) (by positivity)
  obtain ⟨k, hk, hequations⟩ := choose_equations q (ε / 16) (by positivity) (4 * (E + 1) ^ 2)
  let δ := (ε / 16) / (q + 1)
  have hδ : 0 < δ := div_pos (by positivity) (by linarith)
  have hδmul : δ * (q + 1) = ε / 16 := div_mul_cancel₀ _ (by linarith : q + 1 ≠ 0)
  have hδq : q * δ ≤ ε / 16 := by nlinarith
  refine ⟨E, k, δ, hE, hk, hδ, ?_, ?_⟩
  · have h : 2 * (q / Real.sqrt ((2 : ℝ) ^ k)) + q * δ ≤ ε / 2 := by linarith
    simpa only [mul_div_assoc] using h
  · nlinarith

end PaperP1.SurfaceCountParameters
