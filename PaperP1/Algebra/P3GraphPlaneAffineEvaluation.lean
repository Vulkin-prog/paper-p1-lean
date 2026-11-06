module

public import PaperP1.Algebra.P3GraphPlaneSection
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! # Literal graph-plane affine points evaluate the original equation exactly -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneAffineEvaluation

open MvPolynomial P3GraphPlaneSection
open scoped Classical

variable {F : Type*} [CommRing F]

def graphPoint (a : Fin 3 → F) (u : Fin 2 → F) : Fin 3 → F :=
  Fin.cons (a 0 * u 0 + a 1 * u 1 + a 2) u

theorem projective_evaluation (a : Fin 3 → F) (u : Fin 3 → F) (P : MvPolynomial (Fin 4) F) :
    eval u (planeSection a P) = eval (Fin.cons (∑ i, a i * u i) u) P := by
  have he : (eval u).comp (planeSection a) = eval (Fin.cons (∑ i, a i * u i) u) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [planeSection]
    · intro i
      cases i using Fin.cases <;> simp [planeSection, coordinates, form]
  exact RingHom.congr_fun he P

theorem affine_coordinates (a : Fin 3 → F) (u : Fin 2 → F) :
    Fin.cons (α := fun _ ↦ F) (∑ i : Fin 3, a i * (Fin.snoc (α := fun _ ↦ F) u 1) i)
      (Fin.snoc (α := fun _ ↦ F) u 1) = Fin.snoc (α := fun _ ↦ F) (graphPoint a u) 1 := by
  have hs : (∑ i : Fin 3, a i * (Fin.snoc (α := fun _ ↦ F) u 1) i) =
      a 0 * u 0 + a 1 * u 1 + a 2 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one, Fin.sum_univ_two]
    rfl
  rw [hs]
  exact Fin.cons_snoc_eq_snoc_cons _ _ _

theorem affine_evaluation (a : Fin 3 → F) (u : Fin 2 → F) (P : MvPolynomial (Fin 4) F) :
    eval (Fin.snoc u 1) (planeSection a P) = eval (Fin.snoc (graphPoint a u) 1) P := by
  rw [projective_evaluation, affine_coordinates]

end PaperP1.P3GraphPlaneAffineEvaluation
