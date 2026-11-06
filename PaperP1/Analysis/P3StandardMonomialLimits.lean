module

public import PaperP1.Analysis.PolynomialNatRatioLimits
public import PaperP1.Algebra.P3StandardMonomialParameters

/-! # Exact leading asymptotics of the actual standard surface monomial size and height weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardMonomialLimits

open Filter Topology P3StandardMonomialParameters Polynomial

theorem size_real (d e : ℕ) (he : d ≤ e) :
    (size d e : ℝ) = ((d : ℝ) / 2) * (e : ℝ) ^ 2 + ((4 * (d : ℝ) - (d : ℝ) ^ 2) / 2) * (e : ℝ) +
      ((d : ℝ) ^ 3 - 6 * (d : ℝ) ^ 2 + 11 * (d : ℝ)) / 6 := by
  have h := size_polynomial d e he
  simp only [ProjectiveHypersurfaceHilbert.polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
  have hr := congrArg (fun x : ℚ ↦ (x : ℝ)) h
  push_cast at hr
  exact hr

theorem weight_real (d e : ℕ) (he : d ≤ e) :
    (weight d e : ℝ) = ((d : ℝ) / 3) * (e : ℝ) ^ 3 +
      ((5 * (d : ℝ) - (d : ℝ) ^ 2) / 4) * (e : ℝ) ^ 2 +
        ((11 * (d : ℝ) - 3 * (d : ℝ) ^ 2) / 12) * (e : ℝ) +
          ((d : ℝ) ^ 4 - 6 * (d : ℝ) ^ 3 + 11 * (d : ℝ) ^ 2 - 6 * (d : ℝ)) / 24 := by
  have h := weight_polynomial d e he
  simp only [P3StandardMonomialWeightPolynomial.polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
  have hr := congrArg (fun x : ℚ ↦ (x : ℝ)) h
  push_cast at hr
  exact hr

theorem size_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ (size d e : ℝ) / (e : ℝ) ^ 2) atTop (𝓝 ((d : ℝ) / 2)) := by
  apply (PolynomialNatRatioLimits.quadratic ((d : ℝ) / 2) ((4 * (d : ℝ) - (d : ℝ) ^ 2) / 2)
    (((d : ℝ) ^ 3 - 6 * (d : ℝ) ^ 2 + 11 * (d : ℝ)) / 6)).congr'
  filter_upwards [eventually_ge_atTop d] with e he
  rw [size_real d e he]

theorem weight_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ (weight d e : ℝ) / (e : ℝ) ^ 3) atTop (𝓝 ((d : ℝ) / 3)) := by
  apply (PolynomialNatRatioLimits.cubic ((d : ℝ) / 3) ((5 * (d : ℝ) - (d : ℝ) ^ 2) / 4)
    ((11 * (d : ℝ) - 3 * (d : ℝ) ^ 2) / 12)
    (((d : ℝ) ^ 4 - 6 * (d : ℝ) ^ 3 + 11 * (d : ℝ) ^ 2 - 6 * (d : ℝ)) / 24)).congr'
  filter_upwards [eventually_ge_atTop d] with e he
  rw [weight_real d e he]

end PaperP1.P3StandardMonomialLimits
