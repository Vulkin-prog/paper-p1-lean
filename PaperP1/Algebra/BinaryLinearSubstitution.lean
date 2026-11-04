module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring

/-! # Exact polynomial coordinate changes induced by inverse binary matrices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLinearSubstitution

open Finset MvPolynomial

variable {R : Type*} [CommRing R]

def linearForm (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) : MvPolynomial (Fin 2) R :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

def substitute (A : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R := MvPolynomial.aeval (linearForm A)

theorem substitute_C (A : Matrix (Fin 2) (Fin 2) R) (r : R) :
    substitute A (MvPolynomial.C r) = MvPolynomial.C r := by simp [substitute]

theorem substitute_X (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    substitute A (MvPolynomial.X i) = linearForm A i := by simp [substitute]

theorem linearForm_one (i : Fin 2) : linearForm (1 : Matrix (Fin 2) (Fin 2) R) i = MvPolynomial.X i := by
  fin_cases i <;> simp [linearForm, Matrix.one_apply]

theorem substitute_one : substitute (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R (MvPolynomial (Fin 2) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [substitute_X, AlgHom.id_apply] using linearForm_one (R := R) i

theorem substitute_linearForm (A B : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    substitute A (linearForm B i) = linearForm (B * A) i := by
  simp [linearForm, Fin.sum_univ_two, map_add, map_mul, substitute_X, Matrix.mul_apply]
  ring

theorem substitute_comp (A B : Matrix (Fin 2) (Fin 2) R) :
    (substitute A).comp (substitute B) = substitute (B * A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, substitute_X] using substitute_linearForm A B i

def equiv (A B : Matrix (Fin 2) (Fin 2) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R where
  toFun := substitute A
  map_mul' := (substitute A).map_mul
  map_add' := (substitute A).map_add
  commutes' := (substitute A).commutes
  invFun := substitute B
  left_inv := by
    intro F
    have h := congrArg (fun φ : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R ↦ φ F)
      (substitute_comp B A)
    simpa only [AlgHom.comp_apply, hAB, substitute_one, AlgHom.id_apply] using h
  right_inv := by
    intro F
    have h := congrArg (fun φ : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R ↦ φ F)
      (substitute_comp A B)
    simpa only [AlgHom.comp_apply, hBA, substitute_one, AlgHom.id_apply] using h

theorem substitute_nonzero (A B : Matrix (Fin 2) (Fin 2) R) (hAB : A * B = 1) (hBA : B * A = 1)
    (F : MvPolynomial (Fin 2) R) (hF : F ≠ 0) : substitute A F ≠ 0 := by
  intro hz
  apply hF
  apply (equiv A B hAB hBA).injective
  change substitute A F = substitute A 0
  simpa only [map_zero] using hz

theorem linearForm_homogeneous (A : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (linearForm A i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X R j).C_mul (A i j)

theorem substitute_homogeneous (A : Matrix (Fin 2) (Fin 2) R) (F : MvPolynomial (Fin 2) R)
    (d : ℕ) (hF : F.IsHomogeneous d) : (substitute A F).IsHomogeneous d := by
  simpa only [substitute, one_mul] using hF.aeval (linearForm A) (linearForm_homogeneous A)

theorem evaluation (A : Matrix (Fin 2) (Fin 2) R) (F : MvPolynomial (Fin 2) R) (z : Fin 2 → R) :
    MvPolynomial.eval z (substitute A F) = MvPolynomial.eval (A.mulVec z) F := by
  have he : (MvPolynomial.eval z).comp (substitute A).toRingHom = MvPolynomial.eval (A.mulVec z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.eval z (substitute A (MvPolynomial.C r)) = MvPolynomial.eval (A.mulVec z) (MvPolynomial.C r)
      rw [substitute_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
    · intro i
      change MvPolynomial.eval z (substitute A (MvPolynomial.X i)) = MvPolynomial.eval (A.mulVec z) (MvPolynomial.X i)
      rw [substitute_X]
      simp only [linearForm, MvPolynomial.eval_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rfl
  exact congrArg (fun φ : MvPolynomial (Fin 2) R →+* R ↦ φ F) he

end PaperP1.BinaryLinearSubstitution
