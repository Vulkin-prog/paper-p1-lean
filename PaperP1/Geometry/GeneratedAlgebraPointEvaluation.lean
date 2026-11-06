module

public import PaperP1.Algebra.GradedPolynomialPresentation
public import PaperP1.Geometry.QuotientPointEvaluation

/-! # Actual coordinate solutions evaluate the original generated graded algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneratedAlgebraPointEvaluation

open MvPolynomial GradedPolynomialPresentation

variable {F A σ : Type*} [Field F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A)
  (hx : ∀ i, x i ∈ H 1) (hgen : Algebra.adjoin F (Set.range x) = ⊤)

def evaluation (w : σ → F) (hw : ∀ P ∈ kernel (F := F) x, eval w P = 0) : A →ₐ[F] F :=
  (QuotientPointEvaluation.evaluation (kernel (F := F) x) w hw).comp
    (toSource H x hx hgen).symm.toAlgHom

theorem evaluation_polynomial (w : σ → F)
    (hw : ∀ P ∈ kernel (F := F) x, eval w P = 0) (P : MvPolynomial σ F) :
    evaluation H x hx hgen w hw (aeval (R := F) x P) = eval w P := by
  change QuotientPointEvaluation.evaluation (kernel (F := F) x) w hw
    ((toSource H x hx hgen).symm (aeval x P)) = eval w P
  rw [← toSource_mk H x hx hgen P, AlgEquiv.symm_apply_apply]
  rfl

theorem evaluation_coordinate (w : σ → F)
    (hw : ∀ P ∈ kernel (F := F) x, eval w P = 0) (i : σ) :
    evaluation H x hx hgen w hw (x i) = w i := by
  simpa only [aeval_X, eval_X] using evaluation_polynomial H x hx hgen w hw (X i)

theorem points_equal (w v : σ → F)
    (hw : ∀ P ∈ kernel (F := F) x, eval w P = 0)
    (hv : ∀ P ∈ kernel (F := F) x, eval v P = 0)
    (he : evaluation H x hx hgen w hw = evaluation H x hx hgen v hv) : w = v := by
  funext i
  have hh := DFunLike.congr_fun he (x i)
  simpa only [evaluation_coordinate] using hh

end PaperP1.GeneratedAlgebraPointEvaluation
