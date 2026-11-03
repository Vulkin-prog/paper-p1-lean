module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # A rational graph with constant nonzero denominator and numerator degree at most one is an actual affine line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearRationalGraph

open Polynomial

variable {F : Type*} [Field F]

theorem exists_parameters (p q : F[X]) (hp : p.natDegree ≤ 1) (hq : q.natDegree = 0) (hq0 : q ≠ 0) :
    ∃ α β : F, ∀ X Y : F, (p.eval X = Y * q.eval X ↔ Y = α * X + β) := by
  obtain ⟨a, b, hpform⟩ := exists_eq_X_add_C_of_natDegree_le_one hp
  have hqform : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hq
  have hc : q.coeff 0 ≠ 0 := by
    intro hz
    exact hq0 (hqform.trans (by rw [hz, C_0]))
  refine ⟨a / q.coeff 0, b / q.coeff 0, fun X Y ↦ ?_⟩
  have hpval : p.eval X = a * X + b := by
    rw [hpform]
    simp only [eval_add, eval_mul, eval_C, eval_X]
  have hqval : q.eval X = q.coeff 0 := (congrArg (Polynomial.eval X) hqform).trans eval_C
  have hfrac : a / q.coeff 0 * X + b / q.coeff 0 = (a * X + b) / q.coeff 0 := by
    field_simp
  rw [hpval, hqval, hfrac, eq_div_iff hc]
  exact eq_comm

end PaperP1.LinearRationalGraph
