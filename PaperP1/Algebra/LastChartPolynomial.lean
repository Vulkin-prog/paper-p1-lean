module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring

/-! # Literal polynomial evaluation on the projective chart whose last coordinate is one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LastChartPolynomial

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

def dehomogenize : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  eval₂Hom C (Fin.snoc X 1)

theorem evaluation (P : MvPolynomial (Fin (n + 1)) R) (v : Fin n → R) :
    eval v (dehomogenize P) = eval (Fin.snoc v 1) P := by
  have he : (eval v).comp (dehomogenize (R := R) (n := n)) = eval (Fin.snoc v 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenize]
    · intro i
      cases i using Fin.lastCases <;> simp [dehomogenize]
  exact RingHom.congr_fun he P

theorem pderiv (P : MvPolynomial (Fin (n + 1)) R) (i : Fin n) :
    MvPolynomial.pderiv i (dehomogenize P) = dehomogenize (MvPolynomial.pderiv i.castSucc P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [dehomogenize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, MvPolynomial.pderiv_mul, hP]
    cases j using Fin.lastCases with
    | last => simp [dehomogenize]
    | cast j =>
      by_cases hj : j = i <;> simp [dehomogenize, hj] <;> ring

end PaperP1.LastChartPolynomial
