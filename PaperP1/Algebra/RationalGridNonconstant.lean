module

public import PaperP1.Algebra.LinearRationalGraph
public import Lean.Elab.Tactic.Omega

/-! # One actual offset match and a positive host exclude a constant rational graph -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGridNonconstant

open Polynomial

theorem degree_pos {F : Type*} [Field F] [CharZero F] (p q : F[X]) (hq : q ≠ 0)
    (i j X Y : ℤ) (hmatch : p.eval (-(i : F)) = -(j : F) * q.eval (-(i : F)))
    (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F)) (hpositive : 0 < Y + j) :
    0 < max p.natDegree q.natDegree := by
  by_contra hnot
  have hpdeg : p.natDegree = 0 := by omega
  have hqdeg : q.natDegree = 0 := by omega
  have hconst (r : F[X]) (hr : r.natDegree = 0) (z : F) : r.eval z = r.coeff 0 :=
    (congrArg (fun f : F[X] ↦ f.eval z) (eq_C_of_natDegree_eq_zero hr)).trans eval_C
  have hqcoef : q.coeff 0 ≠ 0 := by
    intro hz
    exact hq ((eq_C_of_natDegree_eq_zero hqdeg).trans (by rw [hz, C_0]))
  rw [hconst p hpdeg, hconst q hqdeg] at hmatch hpoint
  have hY : (Y : F) = -(j : F) := mul_right_cancel₀ hqcoef (hpoint.symm.trans hmatch)
  have hzero : Y + j = 0 := by
    apply Int.cast_injective (α := F)
    simp only [Int.cast_add, Int.cast_zero, hY, neg_add_cancel]
  omega

end PaperP1.RationalGridNonconstant
