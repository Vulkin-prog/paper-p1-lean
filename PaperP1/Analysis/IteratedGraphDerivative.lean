module

public import PaperP1.Analysis.GraphTangentEvaluation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Positive-order actual graph derivatives with exact polynomial numerators

The quotient recurrence is verified for every order on an actual open chart.
No analyticity or iterated derivative identity is assumed as an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedGraphDerivative

open Set MvPolynomial PolynomialTangentDegree RationalTangentNumerator GraphTangentEvaluation

theorem quotient_step (a u v w : ℝ) (ha : a ≠ 0) (n : ℕ) :
    ((u / a) * a ^ (2 * n + 1) - v * (((2 * n + 1 : ℕ) : ℝ) * a ^ (2 * n) * (w / a))) /
      (a ^ (2 * n + 1)) ^ 2 =
        (a * u - ((2 * n + 1 : ℕ) : ℝ) * v * w) / a ^ (2 * (n + 1) + 1) := by
  have hb : a ^ (2 * n) ≠ 0 := pow_ne_zero _ ha
  simp only [show 2 * (n + 1) + 1 = 2 * n + 3 by omega, pow_add a (2 * n) 3, pow_succ a (2 * n)]
  field_simp [ha, hb]

theorem numerator_quotient_hasDerivAt (P Q : MvPolynomial (Fin 2) ℝ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hφ : Trajectory P φ s) (n : ℕ)
    (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (fun u ↦ eval (fun j ↦ φ j u) (numerator P Q n) /
      (eval (fun j ↦ φ j u) (pderiv 1 P)) ^ (2 * n + 1))
      (eval (fun j ↦ φ j t) (numerator P Q (n + 1)) /
        (eval (fun j ↦ φ j t) (pderiv 1 P)) ^ (2 * (n + 1) + 1)) t := by
  have hN := hasDerivAt_evaluation P (numerator P Q n) φ s hφ t ht
  have hA := hasDerivAt_evaluation P (pderiv 1 P) φ s hφ t ht
  have hh := HasDerivAt.fun_div hN (HasDerivAt.fun_pow hA (2 * n + 1)) (pow_ne_zero _ (hφ.1 t ht))
  apply hh.congr_deriv
  simpa only [show 2 * n + 1 - 1 = 2 * n by omega, numerator, step, map_sub, map_mul, eval_C] using
    quotient_step (eval (fun j ↦ φ j t) (pderiv 1 P))
      (eval (fun j ↦ φ j t) (tangent P (numerator P Q n)))
      (eval (fun j ↦ φ j t) (numerator P Q n))
      (eval (fun j ↦ φ j t) (tangent P (pderiv 1 P))) (hφ.1 t ht) n

theorem iterated_evaluation (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) (n : ℕ) :
    EqOn (iteratedDeriv (n + 1) (fun u ↦ eval (fun j ↦ φ j u) Q))
      (fun t ↦ eval (fun j ↦ φ j t) (numerator P Q n) /
        (eval (fun j ↦ φ j t) (pderiv 1 P)) ^ (2 * n + 1)) s := by
  induction n with
  | zero =>
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    simpa only [numerator, Nat.mul_zero, Nat.zero_add, pow_one] using
      deriv_evaluation P Q φ s hφ t ht
  | succ n ih =>
    have he := ih.deriv hs
    intro t ht
    rw [iteratedDeriv_succ]
    exact (he ht).trans (numerator_quotient_hasDerivAt P Q φ s hφ n t ht).deriv

theorem positive_order (P Q : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s) (j : ℕ) (hj : 1 ≤ j) :
    ∃ N : MvPolynomial (Fin 2) ℝ, N.totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * j ∧
      EqOn (iteratedDeriv j (fun u ↦ eval (fun i ↦ φ i u) Q))
        (fun t ↦ eval (fun i ↦ φ i t) N / (eval (fun i ↦ φ i t) (pderiv 1 P)) ^ (2 * j - 1)) s := by
  refine ⟨numerator P Q (j - 1), ?_, ?_⟩
  · have hh := numerator_degree P Q (j - 1)
    rwa [show j - 1 + 1 = j by omega] at hh
  · have hh := iterated_evaluation P Q φ s hs hφ (j - 1)
    simpa only [show j - 1 + 1 = j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega] using hh

end PaperP1.IteratedGraphDerivative
