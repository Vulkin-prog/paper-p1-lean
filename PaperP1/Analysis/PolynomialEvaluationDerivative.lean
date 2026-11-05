module

public import PaperP1.Algebra.PolynomialTangentDegree
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual differentiation and smoothness of multivariate polynomial evaluation

The directional derivative is the finite sum of evaluated formal partials.
The chain rule is proved from constants, addition and multiplication by a variable.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialEvaluationDerivative

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ]

def directional (z v : σ → ℝ) (Q : MvPolynomial σ ℝ) : ℝ :=
  ∑ i, eval z (pderiv i Q) * v i

theorem directional_constant (z v : σ → ℝ) (r : ℝ) : directional z v (C r) = 0 := by
  simp only [directional, pderiv_C, map_zero, zero_mul, sum_const_zero]

theorem directional_variable (z v : σ → ℝ) (j : σ) : directional z v (X j) = v j := by
  classical
  simp [directional, pderiv_X, Pi.single_apply]

theorem directional_add (z v : σ → ℝ) (P Q : MvPolynomial σ ℝ) :
    directional z v (P + Q) = directional z v P + directional z v Q := by
  simp only [directional, map_add, add_mul, sum_add_distrib]

theorem directional_mul (z v : σ → ℝ) (P Q : MvPolynomial σ ℝ) :
    directional z v (P * Q) = directional z v P * eval z Q + eval z P * directional z v Q := by
  simp only [directional, pderiv_mul, map_add, map_mul, add_mul, sum_add_distrib]
  congr 1
  · rw [sum_mul]
    apply sum_congr rfl
    intro i _hi
    ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro i _hi
    ring

theorem hasDerivAt_eval (Q : MvPolynomial σ ℝ) (f : σ → ℝ → ℝ) (v : σ → ℝ) (x : ℝ)
    (hf : ∀ i, HasDerivAt (f i) (v i) x) :
    HasDerivAt (fun t ↦ eval (fun i ↦ f i t) Q) (directional (fun i ↦ f i x) v Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C r => simpa only [eval_C, directional_constant] using hasDerivAt_const x r
  | add P Q hP hQ =>
    simp only [map_add, directional_add]
    exact HasDerivAt.fun_add hP hQ
  | mul_X P i hP =>
    simp only [map_mul, eval_X, directional_mul, directional_variable]
    exact HasDerivAt.fun_mul hP (hf i)

omit [Fintype σ] in
theorem contDiffOn_eval (Q : MvPolynomial σ ℝ) (n : WithTop ℕ∞) (s : Set ℝ)
    (f : σ → ℝ → ℝ) (hf : ∀ i, ContDiffOn ℝ n (f i) s) :
    ContDiffOn ℝ n (fun t ↦ eval (fun i ↦ f i t) Q) s := by
  induction Q using MvPolynomial.induction_on with
  | C r => simpa only [eval_C] using (contDiffOn_const (c := r) : ContDiffOn ℝ n (fun _ ↦ r) s)
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP => simpa only [map_mul, eval_X] using hP.mul (hf i)

end PaperP1.PolynomialEvaluationDerivative
