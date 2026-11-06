module

public import PaperP1.Arithmetic.SmoothIntegerSurfaceBranch
public import PaperP1.Algebra.IteratedBivariatePolynomialDeterminant
public import Mathlib.Algebra.Polynomial.Div

/-! # The actual determinant divisor on a smooth surface congruence class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothSurfaceDeterminant

open Polynomial

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def substitution (a b : R) (q : R[X][X]) : R[X][X][X] →+* R[X][X] :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        (Polynomial.C (Polynomial.C a + Polynomial.X)))
      (Polynomial.C (Polynomial.C b) + Polynomial.X)) q

theorem substitution_eval (a b : R) (q : R[X][X]) (F : R[X][X][X]) (t u : R) :
    (substitution a b q F).evalEval t u =
      TernaryPolynomialEvaluation.evaluation (a + t) (b + u) (q.evalEval t u) F := by
  have he : (Polynomial.evalEvalRingHom t u).comp (substitution a b q) =
      TernaryPolynomialEvaluation.evaluation (a + t) (b + u) (q.evalEval t u) := by
    ext <;> simp [substitution, TernaryPolynomialEvaluation.evaluation, RingHom.comp_apply]
  exact RingHom.congr_fun he F

theorem nilpotent_surface_dvd (p : R) (N : ℕ) (hN : (Ideal.span {p} : Ideal R) ^ N = ⊥)
    (P : R[X][X][X]) (a b c : R)
    (hP : TernaryPolynomialEvaluation.evaluation a b c P ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p})
      (TernaryPolynomialEvaluation.evaluation a b c P.derivative)))
    (L : ℕ) (x y z : ι → R) (hx : ∀ j, p ∣ x j - a)
    (hy : ∀ j, p ∣ y j - b) (hz : ∀ j, p ∣ z j - c)
    (hroots : ∀ j, TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) P = 0)
    (F : ι → R[X][X][X]) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      Matrix.det (fun i j ↦ TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i)) := by
  obtain ⟨q, hq⟩ := TernaryNilpotentImplicitFunction.exists_polynomial_implicit
    (Ideal.span {p}) N hN P a b c hP hder
  have hvalue (j : ι) : z j = q.evalEval (x j - a) (y j - b) :=
    hq (x j) (y j) (z j) (Ideal.mem_span_singleton.mpr (hx j))
      (Ideal.mem_span_singleton.mpr (hy j)) (Ideal.mem_span_singleton.mpr (hz j)) (hroots j)
  let Q : ι → R[X][X] := fun i ↦ substitution a b q (F i)
  have he : (fun i j ↦ TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i)) =
      (fun i j ↦ (Q i).evalEval (x j - a) (y j - b)) := by
    funext i j
    change TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i) =
      (substitution a b q (F i)).evalEval (x j - a) (y j - b)
    have hcx : a + (x j - a) = x j := by ring
    have hcy : b + (y j - b) = y j := by ring
    rw [substitution_eval, hcx, hcy, ← hvalue]
  rw [he]
  exact IteratedBivariatePolynomialDeterminant.polynomial_dvd p Q L
    (fun j ↦ x j - a) (fun j ↦ y j - b) hx hy

theorem smooth_surface_det_zero (p : R) (L : ℕ)
    (hp : p ^ (L * Fintype.card ι - (L + 2).choose 3) = 0)
    (P : R[X][X][X]) (a b c : R)
    (hP : TernaryPolynomialEvaluation.evaluation a b c P ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p})
      (TernaryPolynomialEvaluation.evaluation a b c P.derivative)))
    (x y z : ι → R) (hx : ∀ j, p ∣ x j - a) (hy : ∀ j, p ∣ y j - b)
    (hz : ∀ j, p ∣ z j - c)
    (hroots : ∀ j, TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) P = 0)
    (F : ι → R[X][X][X]) :
    Matrix.det (fun i j ↦ TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i)) = 0 := by
  have hN : (Ideal.span {p} : Ideal R) ^ (L * Fintype.card ι - (L + 2).choose 3) = ⊥ := by
    rw [Ideal.span_singleton_pow, hp, Ideal.span_singleton_zero]
  have hd := nilpotent_surface_dvd p (L * Fintype.card ι - (L + 2).choose 3)
    hN P a b c hP hder L x y z hx hy hz hroots F
  rw [hp] at hd
  exact zero_dvd_iff.mp hd

theorem integer_smooth_dvd (p L : ℕ) (hp : p.Prime) (P : ℤ[X][X][X]) (a b c : ℤ)
    (hP : (p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P)
    (hder : ¬(p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P.derivative)
    (x y z : ι → ℤ) (hx : ∀ j, (p : ℤ) ∣ x j - a) (hy : ∀ j, (p : ℤ) ∣ y j - b)
    (hz : ∀ j, (p : ℤ) ∣ z j - c)
    (hroots : ∀ j, TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) P = 0)
    (F : ι → ℤ[X][X][X]) :
    (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      Matrix.det (fun i j ↦ TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i)) := by
  obtain ⟨q, hq⟩ := SmoothIntegerSurfaceBranch.implicit_mod_prime_power
    p (L * Fintype.card ι - (L + 2).choose 3) hp P a b c hP hder
  let Q : ι → ℤ[X][X] := fun i ↦ substitution a b q (F i)
  have hentry (i j : ι) : (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i) -
        (Q i).evalEval (x j - a) (y j - b) := by
    have hd := (hq (x j) (y j) (z j) (hx j) (hy j) (hz j) (hroots j)).trans
      (Polynomial.sub_dvd_eval_sub (z j) (q.evalEval (x j - a) (y j - b))
        ((F i).map (Polynomial.evalEvalRingHom (x j) (y j))))
    change (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i) -
        (substitution a b q (F i)).evalEval (x j - a) (y j - b)
    have hcx : a + (x j - a) = x j := by ring
    have hcy : b + (y j - b) = y j := by ring
    rw [substitution_eval, hcx, hcy]
    simpa only [Polynomial.eval_map, TernaryPolynomialEvaluation.evaluation,
      Polynomial.coe_eval₂RingHom] using hd
  exact IteratedBivariatePolynomialDeterminant.congruent_polynomial_dvd (p : ℤ) Q L
    (fun j ↦ x j - a) (fun j ↦ y j - b) hx hy
    (fun i j ↦ TernaryPolynomialEvaluation.evaluation (x j) (y j) (z j) (F i)) hentry

end PaperP1.SmoothSurfaceDeterminant
