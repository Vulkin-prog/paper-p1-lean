module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.Tactic.FieldSimp

/-! # Actual radial fibres of a quadratic equation at a smooth origin -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticDirectionFibres

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

def direction (v : Fin (n + 1) → F) : Fin n → F :=
  fun i ↦ v i.succ / v 0

theorem reconstruct (v : Fin (n + 1) → F) (hv : v 0 ≠ 0) :
    v = fun i ↦ v 0 * Fin.cons (α := fun _ ↦ F) 1 (direction v) i := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp only [Fin.cons_succ, direction]; field_simp

theorem root_direction (a : F) (Q : MvPolynomial (Fin (n + 1)) F)
    (hQ : Q.IsHomogeneous 2) (v : Fin (n + 1) → F) (hv : v 0 ≠ 0)
    (hroot : a * v 0 + eval v Q = 0) :
    a + v 0 * eval (Fin.cons 1 (direction v)) Q = 0 := by
  have he : eval v Q = v 0 ^ 2 * eval (Fin.cons 1 (direction v)) Q := by
    conv_lhs => rw [reconstruct v hv]
    exact HomogeneousPolynomialEvaluation.eval_scale Q hQ _ _
  rw [he] at hroot
  apply (mul_eq_zero.mp (show v 0 * (a + v 0 * eval (Fin.cons 1 (direction v)) Q) = 0 from ?_)).resolve_left hv
  calc
    _ = a * v 0 + v 0 ^ 2 * eval (Fin.cons 1 (direction v)) Q := by ring
    _ = 0 := hroot

theorem injective_on_roots (a : F) (ha : a ≠ 0)
    (Q : MvPolynomial (Fin (n + 1)) F) (hQ : Q.IsHomogeneous 2)
    (v w : Fin (n + 1) → F) (hv : v 0 ≠ 0) (hw : w 0 ≠ 0)
    (hvr : a * v 0 + eval v Q = 0) (hwr : a * w 0 + eval w Q = 0)
    (hdir : direction v = direction w) : v = w := by
  have hvr' := root_direction a Q hQ v hv hvr
  have hwr' := root_direction a Q hQ w hw hwr
  rw [← hdir] at hwr'
  have hc : eval (Fin.cons 1 (direction v)) Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero, add_zero] at hvr'
    exact ha hvr'
  have hfirst : v 0 = w 0 := by
    apply mul_right_cancel₀ hc
    exact add_left_cancel (hvr'.trans hwr'.symm)
  rw [reconstruct v hv, reconstruct w hw, hfirst, hdir]

end PaperP1.QuadraticDirectionFibres
