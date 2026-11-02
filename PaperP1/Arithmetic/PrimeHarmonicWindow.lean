module

public import PaperP1.Arithmetic.PrimeLogMertens
public import PaperP1.Analysis.LogarithmicAbelWindow

/-! # An actual prime harmonic window with a uniform inverse-logarithm error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeHarmonicWindow

open Finset

def harmonic (a b : ℝ) : ℝ :=
  ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / (p : ℝ)

theorem prime_coefficient (p : ℕ) (hp : p.Prime) :
    (Real.log (p : ℝ))⁻¹ * PrimeLogMertens.coefficient p = 1 / (p : ℝ) := by
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  rw [PrimeLogMertens.coefficient, ite_eq_left hp, ← mul_div_assoc, inv_mul_cancel₀ hlog]

theorem abel_sum_eq_harmonic (a b : ℝ) :
    (∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log (p : ℝ))⁻¹ * PrimeLogMertens.coefficient p) = harmonic a b := by
  rw [harmonic, sum_filter]
  apply sum_congr rfl
  intro p _hp
  by_cases hp : p.Prime
  · rw [ite_eq_left hp]
    exact prime_coefficient p hp
  · simp only [PrimeLogMertens.coefficient, ite_eq_right hp, mul_zero]

theorem finite_window_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    |harmonic a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤
      2 * PrimeLogMertens.budget / Real.log a := by
  have h := LogarithmicAbelWindow.window_bound PrimeLogMertens.coefficient a b PrimeLogMertens.budget
    (by linarith) hab (fun t ht ↦ PrimeLogMertens.prefix_error t (ha.trans ht.1))
  rwa [abel_sum_eq_harmonic] at h

end PaperP1.PrimeHarmonicWindow
