module

public import PaperP1.Algebra.HomogeneousLinearForm
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Pi

/-! # Polynomial coordinate changes induced by literal linear maps and equivalences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearMapPolynomialCoordinates

open MvPolynomial Finset
open scoped Classical

variable {F σ : Type*} [Field F] [Fintype σ] [DecidableEq σ]

def coordinate (f : (σ → F) →ₗ[F] (σ → F)) (i : σ) : MvPolynomial σ F :=
  ∑ j, C (f (Pi.single j 1) i) * X j

def substitute (f : (σ → F) →ₗ[F] (σ → F)) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  aeval (coordinate f)

theorem coordinate_evaluation (f : (σ → F) →ₗ[F] (σ → F)) (i : σ) (v : σ → F) :
    eval v (coordinate f i) = f v i := by
  have hv : v = ∑ j, v j • Pi.single j (1 : F) := by
    funext k
    simp [Pi.single_apply]
  have he := congrArg (fun w : σ → F ↦ w i) (congrArg f hv)
  rw [map_sum] at he
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  simp only [coordinate, map_sum, map_mul, eval_C, eval_X]
  apply sum_congr rfl
  intro j _
  ring

theorem evaluation (f : (σ → F) →ₗ[F] (σ → F)) (P : MvPolynomial σ F) (v : σ → F) :
    eval v (substitute f P) = eval (f v) P := by
  have he : (eval v).comp (substitute f).toRingHom = eval (f v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [substitute]
    · intro i
      rw [RingHom.comp_apply, eval_X]
      change eval v (aeval (R := F) (coordinate f) (X i : MvPolynomial σ F)) = f v i
      rw [aeval_X]
      exact coordinate_evaluation f i v
  exact RingHom.congr_fun he P

theorem homogeneous (f : (σ → F) →ₗ[F] (σ → F)) (P : MvPolynomial σ F) {d : ℕ}
    (hP : P.IsHomogeneous d) : (substitute f P).IsHomogeneous d := by
  have hc : ∀ i, (coordinate f i).IsHomogeneous 1 := by
    intro i
    apply IsHomogeneous.sum
    intro j _
    exact (isHomogeneous_X F j).C_mul _
  simpa only [substitute, one_mul] using hP.aeval (coordinate f) hc

def equiv [Infinite F] (e : (σ → F) ≃ₗ[F] (σ → F)) : MvPolynomial σ F ≃ₐ[F] MvPolynomial σ F where
  toFun := substitute e.toLinearMap
  invFun := substitute e.symm.toLinearMap
  left_inv P := by
    apply MvPolynomial.funext
    intro v
    rw [evaluation, evaluation]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  right_inv P := by
    apply MvPolynomial.funext
    intro v
    rw [evaluation, evaluation]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  map_mul' := (substitute e.toLinearMap).map_mul
  map_add' := (substitute e.toLinearMap).map_add
  commutes' := (substitute e.toLinearMap).commutes

end PaperP1.LinearMapPolynomialCoordinates
