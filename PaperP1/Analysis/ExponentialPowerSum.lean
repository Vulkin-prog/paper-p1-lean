module

public import PaperP1.Probability.PoissonExponential

/-! # An exponential majorant for every factorial-weighted power sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExponentialPowerSum

def term (m : ℕ) (z : ℝ) (r : ℕ) : ℝ := (r : ℝ) ^ m * z ^ r / (r.factorial : ℝ)

def total (m : ℕ) (z : ℝ) : ℝ := ∑' r : ℕ, term m z r

theorem hasSum_exp_series (z : ℝ) :
    HasSum (fun r : ℕ ↦ z ^ r / (r.factorial : ℝ)) (Real.exp z) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp z

theorem term_nonneg (m : ℕ) (z : ℝ) (hz : 0 ≤ z) (r : ℕ) : 0 ≤ term m z r := by
  unfold term
  positivity

theorem power_le_factorial_exp (m r : ℕ) : (r : ℝ) ^ m ≤ (m.factorial : ℝ) * Real.exp r := by
  have h := Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) m
  have hf : (0 : ℝ) < m.factorial := by positivity
  have h' := (div_le_iff₀ hf).mp h
  simpa only [mul_comm] using h'

theorem term_le_majorant (m : ℕ) (z : ℝ) (hz : 0 ≤ z) (r : ℕ) :
    term m z r ≤ (m.factorial : ℝ) * ((Real.exp 1 * z) ^ r / (r.factorial : ℝ)) := by
  have h := mul_le_mul_of_nonneg_right (power_le_factorial_exp m r)
    (by positivity : (0 : ℝ) ≤ z ^ r / (r.factorial : ℝ))
  calc
    _ = (r : ℝ) ^ m * (z ^ r / (r.factorial : ℝ)) := by unfold term; ring
    _ ≤ ((m.factorial : ℝ) * Real.exp r) * (z ^ r / (r.factorial : ℝ)) := h
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_one]
      ring

theorem summable_term (m : ℕ) (z : ℝ) (hz : 0 ≤ z) : Summable (term m z) :=
  ((hasSum_exp_series (Real.exp 1 * z)).mul_left (m.factorial : ℝ)).summable.of_nonneg_of_le
    (term_nonneg m z hz) (term_le_majorant m z hz)

theorem total_le (m : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    total m z ≤ (m.factorial : ℝ) * Real.exp (Real.exp 1 * z) := by
  have hmajor := (hasSum_exp_series (Real.exp 1 * z)).mul_left (m.factorial : ℝ)
  calc
    _ ≤ ∑' r : ℕ, (m.factorial : ℝ) * ((Real.exp 1 * z) ^ r / (r.factorial : ℝ)) :=
      (summable_term m z hz).tsum_le_tsum (term_le_majorant m z hz) hmajor.summable
    _ = _ := hmajor.tsum_eq

end PaperP1.ExponentialPowerSum
