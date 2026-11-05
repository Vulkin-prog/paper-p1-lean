module

public import PaperP1.Arithmetic.SmoothIntegerCongruenceBranch
public import PaperP1.Algebra.PolynomialResidueDeterminant

/-! # The determinant divisor for actual points in a smooth affine residue class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothCurveDeterminant

open Polynomial PaperP1.PolynomialResidueDeterminant

variable {R : Type*} [CommRing R]

def substitution (a : R) (q : R[X]) : R[X][X] →+* R[X] :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C a)) q

theorem substitution_eval (a : R) (q : R[X]) (F : R[X][X]) (t : R) :
    (substitution a q F).eval t = F.evalEval (a + t) (q.eval t) := by
  have he : (Polynomial.evalRingHom t).comp (substitution a q) =
      Polynomial.evalEvalRingHom (a + t) (q.eval t) := by
    ext <;> simp [substitution, RingHom.comp_apply, add_comm]
  have h := RingHom.congr_fun he F
  simpa only [RingHom.comp_apply, Polynomial.coe_evalRingHom,
    Polynomial.coe_evalEvalRingHom, Polynomial.evalEval] using h

theorem nilpotent_curve_dvd (p : R) (N : ℕ) (hN : (Ideal.span {p} : Ideal R) ^ N = ⊥)
    (P : R[X][X]) (a b : R) (hP : P.evalEval a b ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) (P.derivative.evalEval a b)))
    (k : ℕ) (x y : Fin k → R) (hx : ∀ j, p ∣ x j - a) (hy : ∀ j, p ∣ y j - b)
    (hroots : ∀ j, P.evalEval (x j) (y j) = 0) (F : Fin k → R[X][X]) :
    p ^ (k * (k - 1) / 2) ∣ Matrix.det (fun i j ↦ (F i).evalEval (x j) (y j)) := by
  obtain ⟨q, hq⟩ := BivariateNilpotentImplicitFunction.exists_polynomial_implicit
    (Ideal.span {p}) N hN P a b hP hder
  have hvalue (j : Fin k) : y j = q.eval (x j - a) :=
    hq (x j) (y j) (Ideal.mem_span_singleton.mpr (hx j))
      (Ideal.mem_span_singleton.mpr (hy j)) (hroots j)
  let Q : Fin k → R[X] := fun i ↦ substitution a q (F i)
  have he : (fun i j ↦ (F i).evalEval (x j) (y j)) =
      (fun i j ↦ (Q i).eval (x j - a)) := by
    funext i j
    change (F i).evalEval (x j) (y j) = (substitution a q (F i)).eval (x j - a)
    have hc : a + (x j - a) = x j := by ring
    rw [substitution_eval, hc, ← hvalue]
  rw [he]
  exact polynomial_evaluation_dvd p k Q (fun j ↦ x j - a) hx

theorem smooth_curve_det_zero (p : R) (k : ℕ) (hp : p ^ (k * (k - 1) / 2) = 0)
    (P : R[X][X]) (a b : R) (hP : P.evalEval a b ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) (P.derivative.evalEval a b)))
    (x y : Fin k → R) (hx : ∀ j, p ∣ x j - a) (hy : ∀ j, p ∣ y j - b)
    (hroots : ∀ j, P.evalEval (x j) (y j) = 0) (F : Fin k → R[X][X]) :
    Matrix.det (fun i j ↦ (F i).evalEval (x j) (y j)) = 0 := by
  have hN : (Ideal.span {p} : Ideal R) ^ (k * (k - 1) / 2) = ⊥ := by
    rw [Ideal.span_singleton_pow, hp, Ideal.span_singleton_zero]
  have hd := nilpotent_curve_dvd p (k * (k - 1) / 2) hN P a b hP hder k x y hx hy hroots F
  rw [hp] at hd
  exact zero_dvd_iff.mp hd

theorem integer_smooth_dvd (p k : ℕ) (hp : p.Prime) (P : ℤ[X][X]) (a b : ℤ)
    (hP : (p : ℤ) ∣ P.evalEval a b) (hder : ¬(p : ℤ) ∣ P.derivative.evalEval a b)
    (x y : Fin k → ℤ) (hx : ∀ j, (p : ℤ) ∣ x j - a) (hy : ∀ j, (p : ℤ) ∣ y j - b)
    (hroots : ∀ j, P.evalEval (x j) (y j) = 0) (F : Fin k → ℤ[X][X]) :
    (p : ℤ) ^ (k * (k - 1) / 2) ∣ Matrix.det (fun i j ↦ (F i).evalEval (x j) (y j)) := by
  obtain ⟨q, hq⟩ := SmoothIntegerCongruenceBranch.implicit_mod_prime_power
    p (k * (k - 1) / 2) hp P a b hP hder
  let Q : Fin k → ℤ[X] := fun i ↦ substitution a q (F i)
  have hentry (i j : Fin k) : (p : ℤ) ^ (k * (k - 1) / 2) ∣
      (F i).evalEval (x j) (y j) - (Q i).eval (x j - a) := by
    have hd := (hq (x j) (y j) (hx j) (hy j) (hroots j)).trans
      (Polynomial.sub_dvd_eval_sub (y j) (q.eval (x j - a))
        ((F i).map (Polynomial.evalRingHom (x j))))
    change (p : ℤ) ^ (k * (k - 1) / 2) ∣
      (F i).evalEval (x j) (y j) - (substitution a q (F i)).eval (x j - a)
    have hc : a + (x j - a) = x j := by ring
    rw [substitution_eval, hc]
    simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hd
  exact congruent_polynomial_evaluation_dvd (p : ℤ) k Q (fun j ↦ x j - a)
    (fun i j ↦ (F i).evalEval (x j) (y j)) hx hentry

end PaperP1.SmoothCurveDeterminant
