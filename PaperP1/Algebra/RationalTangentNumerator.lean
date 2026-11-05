module

public import PaperP1.Algebra.PolynomialTangentDegree
public import Mathlib.Basic.Real.Basic

/-! # Exact numerator recurrence for positive-order normalized tangent derivatives

Index `n` corresponds to derivative order `n+1` and denominator exponent `2n+1`.
The expanded mixed term has a minus sign, forced by the tangent operator.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTangentNumerator

open MvPolynomial PolynomialTangentDegree

variable {R : Type*} [CommRing R]

def step (P N : MvPolynomial (Fin 2) R) (e : R) : MvPolynomial (Fin 2) R :=
  pderiv 1 P * tangent P N - C e * N * tangent P (pderiv 1 P)

def numerator (P Q : MvPolynomial (Fin 2) R) : ℕ → MvPolynomial (Fin 2) R
  | 0 => tangent P Q
  | n + 1 => step P (numerator P Q n) ((2 * n + 1 : ℕ) : R)

theorem step_expanded (P N : MvPolynomial (Fin 2) R) (e : R) :
    step P N e = (pderiv 1 P) ^ 2 * pderiv 0 N -
      pderiv 1 P * pderiv 0 P * pderiv 1 N -
      C e * N * (pderiv 1 P * pderiv 0 (pderiv 1 P) - pderiv 0 P * pderiv 1 (pderiv 1 P)) := by
  simp only [step, tangent]
  ring

theorem step_degree (P N : MvPolynomial (Fin 2) R) (e : R) :
    (step P N e).totalDegree ≤ N.totalDegree + 2 * P.totalDegree := by
  have hA := pderiv_degree_le P 1
  have hL := tangent_degree P N
  have hLA := tangent_degree P (pderiv 1 P)
  have hfirst := totalDegree_mul (pderiv 1 P) (tangent P N)
  have hcoeff : (C e * N).totalDegree ≤ N.totalDegree := by
    simpa only [totalDegree_C, zero_add] using totalDegree_mul (C e) N
  have hsecond := totalDegree_mul (C e * N) (tangent P (pderiv 1 P))
  exact (totalDegree_sub _ _).trans (max_le (by omega) (by omega))

theorem numerator_degree (P Q : MvPolynomial (Fin 2) R) (n : ℕ) :
    (numerator P Q n).totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * (n + 1) := by
  induction n with
  | zero =>
    have hh := tangent_degree P Q
    change (tangent P Q).totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * (0 + 1)
    omega
  | succ n ih =>
    calc
      _ ≤ (numerator P Q n).totalDegree + 2 * P.totalDegree := step_degree P _ _
      _ ≤ (Q.totalDegree + 2 * P.totalDegree * (n + 1)) + 2 * P.totalDegree := Nat.add_le_add_right ih _
      _ = _ := by ring

theorem mixed_term_sign_counterexample :
    let P : MvPolynomial (Fin 2) ℝ := X 0 + X 1 + X 0 * X 1
    let N := tangent P (X 1)
    eval (fun _ ↦ 0) P = 0 ∧ eval (fun _ ↦ 0) (pderiv 1 P) = 1 ∧
      eval (fun _ ↦ 0) (numerator P (X 1) 1) = 2 ∧
      eval (fun _ ↦ 0) ((pderiv 1 P) ^ 2 * pderiv 0 N +
        pderiv 1 P * pderiv 0 P * pderiv 1 N -
        N * (pderiv 1 P * pderiv 0 (pderiv 1 P) - pderiv 0 P * pderiv 1 (pderiv 1 P))) = 0 := by
  norm_num [numerator, step, tangent, pderiv_mul, Pi.single_apply]

end PaperP1.RationalTangentNumerator
