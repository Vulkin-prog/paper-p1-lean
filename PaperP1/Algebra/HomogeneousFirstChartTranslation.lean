module

public import PaperP1.Algebra.HomogeneousLinearShear
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Literal first-chart translation and every free partial derivative -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousFirstChartTranslation

open MvPolynomial

variable {F : Type*} [CommRing F] {n : ℕ}

theorem evaluation (a v : Fin n → F) (P : MvPolynomial (Fin (n + 1)) F) :
    eval (Fin.cons 1 v) (HomogeneousLinearShear.substitute a P) =
      eval (Fin.cons 1 (v + a)) P := by
  have he : (eval (Fin.cons 1 v)).comp (HomogeneousLinearShear.substitute a).toRingHom =
      eval (Fin.cons 1 (v + a)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [HomogeneousLinearShear.substitute]
    · intro i
      cases i using Fin.cases <;> simp [HomogeneousLinearShear.substitute]
  exact RingHom.congr_fun he P

theorem free_partial (a : Fin n → F) (P : MvPolynomial (Fin (n + 1)) F) (i : Fin n) :
    pderiv i.succ (HomogeneousLinearShear.substitute a P) =
      HomogeneousLinearShear.substitute a (pderiv i.succ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [HomogeneousLinearShear.substitute]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, pderiv_mul, hP, pderiv_mul, map_add, map_mul, map_mul]
    congr 1
    congr 1
    cases j using Fin.cases with
    | zero => simp [HomogeneousLinearShear.substitute]
    | succ j =>
      by_cases hji : j = i <;> simp [HomogeneousLinearShear.substitute, hji]

theorem origin_free_partial (a : Fin n → F) (P : MvPolynomial (Fin (n + 1)) F) (i : Fin n) :
    eval (Fin.cons 1 0) (pderiv i.succ (HomogeneousLinearShear.substitute a P)) =
      eval (Fin.cons 1 a) (pderiv i.succ P) := by
  rw [free_partial, HomogeneousLinearShear.eval_substitute]

end PaperP1.HomogeneousFirstChartTranslation
