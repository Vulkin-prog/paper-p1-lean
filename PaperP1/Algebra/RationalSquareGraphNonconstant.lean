module

public import PaperP1.Algebra.RationalGraphSquareRoots

/-! # A rational square graph through a positive selected host cannot be constant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalSquareGraphNonconstant

open Polynomial PaperP1.FormalWordPolynomials

variable {F : Type*} [Field F] [CharZero F]

theorem degree_pos (c : F) (j : ℤ) (I : Finset ℤ) (hI : I.Nonempty)
    (p q : F[X]) (hq : q ≠ 0) (hc : c ≠ 0)
    (hsq : IsSquare (RationalGraphSquareRoots.value c (j : F) (linearOver F I) p q))
    (X Y : ℤ) (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F)) (hpositive : 0 < Y + j) :
    0 < max p.natDegree q.natDegree := by
  by_contra hnot
  have hpdeg : p.natDegree = 0 := by omega
  have hqdeg : q.natDegree = 0 := by omega
  have hconst (r : F[X]) (hr : r.natDegree = 0) (z : F) : r.eval z = r.coeff 0 :=
    (congrArg (fun f : F[X] ↦ f.eval z) (eq_C_of_natDegree_eq_zero hr)).trans eval_C
  have hqcoef : q.coeff 0 ≠ 0 := by
    intro hz
    exact hq ((eq_C_of_natDegree_eq_zero hqdeg).trans (by rw [hz, C_0]))
  obtain ⟨i, hi⟩ := hI
  have hqeval : q.eval (-(i : F)) ≠ 0 := by rw [hconst q hqdeg]; exact hqcoef
  have hm := RationalGraphSquareRoots.offset_match c (j : F) I p q hq hc hsq i hi hqeval
  rw [hconst p hpdeg, hconst q hqdeg] at hm hpoint
  have hY : (Y : F) = -(j : F) := mul_right_cancel₀ hqcoef (hpoint.symm.trans hm)
  have hzero : Y + j = 0 := by
    apply Int.cast_injective (α := F)
    simp only [Int.cast_add, Int.cast_zero, hY, neg_add_cancel]
  omega

end PaperP1.RationalSquareGraphNonconstant
