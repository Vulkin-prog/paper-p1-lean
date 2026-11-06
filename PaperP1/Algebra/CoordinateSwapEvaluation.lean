module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Evaluation and partial derivatives under an actual coordinate transposition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateSwapEvaluation

open MvPolynomial

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

theorem evaluation (P : MvPolynomial σ R) (v : σ → R) (i j : σ) :
    eval (fun k ↦ v (Equiv.swap i j k)) (rename (Equiv.swap i j) P) = eval v P := by
  simpa only [Function.comp_def, Equiv.swap_apply_self] using
    eval_rename (Equiv.swap i j) (fun k ↦ v (Equiv.swap i j k)) P

theorem pderiv_swap (P : MvPolynomial σ R) (i j : σ) :
    pderiv j (rename (Equiv.swap i j) P) = rename (Equiv.swap i j) (pderiv i P) := by
  simpa using pderiv_rename (Equiv.swap i j).injective i P

theorem evaluation_partial (P : MvPolynomial σ R) (v : σ → R) (i j : σ) :
    eval (fun k ↦ v (Equiv.swap i j k)) (pderiv j (rename (Equiv.swap i j) P)) =
      eval v (pderiv i P) := by
  rw [pderiv_swap, evaluation]

end PaperP1.CoordinateSwapEvaluation
