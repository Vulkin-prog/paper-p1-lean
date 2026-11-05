module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Literal point evaluation on an actual polynomial coordinate quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuotientPointEvaluation

open MvPolynomial

def evaluation {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (w : σ → F)
    (hw : ∀ P ∈ I, eval w P = 0) : (MvPolynomial σ F ⧸ I) →ₐ[F] F :=
  let hkill : ∀ P, P ∈ I → aeval w P = 0 := fun P hP ↦ hw P hP
  Ideal.Quotient.liftₐ I (aeval w) hkill

theorem evaluation_mk {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (w : σ → F)
    (hw : ∀ P ∈ I, eval w P = 0) (P : MvPolynomial σ F) :
    evaluation I w hw (Ideal.Quotient.mk I P) = eval w P := rfl

theorem evaluation_X {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (w : σ → F)
    (hw : ∀ P ∈ I, eval w P = 0) (i : σ) :
    evaluation I w hw (Ideal.Quotient.mk I (X i)) = w i := by
  rw [evaluation_mk, eval_X]

theorem points_equal {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (w v : σ → F)
    (hw : ∀ P ∈ I, eval w P = 0) (hv : ∀ P ∈ I, eval v P = 0)
    (he : evaluation I w hw = evaluation I v hv) : w = v := by
  funext i
  have hh := DFunLike.congr_fun he (Ideal.Quotient.mk I (X i))
  simpa only [evaluation_X] using hh

end PaperP1.QuotientPointEvaluation
