module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.Ring

/-! # Actual multivariate polynomial values preserve arbitrary scalar congruences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialEvaluationCongruence

open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem eval_sub_dvd (m : R) (v w : σ → R) (hv : ∀ k, m ∣ v k - w k)
    (F : MvPolynomial σ R) : m ∣ eval v F - eval w F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add F G hF hG =>
    rw [map_add, map_add]
    convert dvd_add hF hG using 1; ring
  | mul_X F k hF =>
    rw [map_mul, map_mul, eval_X, eval_X]
    have hd := dvd_add (dvd_mul_of_dvd_left hF (v k))
      (dvd_mul_of_dvd_right (hv k) (eval w F))
    convert hd using 1; ring

theorem dvd_evaluation_iff (m : R) (v w : σ → R) (hv : ∀ k, m ∣ v k - w k)
    (F : MvPolynomial σ R) : m ∣ eval v F ↔ m ∣ eval w F := by
  have hd := eval_sub_dvd m v w hv F
  constructor
  · intro hF
    have hh := dvd_sub hF hd
    convert hh using 1; ring
  · intro hF
    simpa only [sub_add_cancel] using dvd_add hd hF

end PaperP1.PolynomialEvaluationCongruence
