module

public import PaperP1.Algebra.CoordinateSwapEvaluation
public import PaperP1.Algebra.NormalizedP3SurfaceDeterminant

/-! # Exact exchange between the original last chart and a first-coordinate chart over any field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FieldChartExchange

open MvPolynomial
open scoped Classical

variable {F : Type*} [Field F]

def permutation : Equiv.Perm (Fin 4) := Equiv.swap 0 3

def point (v : Fin 3 → F) : Fin 3 → F :=
  fun i ↦ Fin.snoc (α := fun _ ↦ F) v 1 (permutation i.succ)

theorem full_point (v : Fin 3 → F) :
    (Fin.cons 1 (point v) : Fin 4 → F) =
      fun k ↦ Fin.snoc (α := fun _ ↦ F) v 1 (permutation k) := by
  funext k
  cases k using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, permutation, Equiv.swap_apply_left]
    rw [show (3 : Fin 4) = Fin.last 3 by decide, Fin.snoc_last]
  | succ k => rfl

theorem point_injective : Function.Injective (point (F := F)) := by
  intro v w he
  have hh := congrArg (fun u : Fin 3 → F ↦ Fin.cons (α := fun _ ↦ F) 1 u) he
  rw [full_point, full_point] at hh
  have hfull : (Fin.snoc v 1 : Fin 4 → F) = Fin.snoc w 1 := by
    funext k
    have hk := congrFun hh (permutation k)
    simpa only [permutation, Equiv.swap_apply_self] using hk
  funext i
  simpa only [Fin.snoc_castSucc] using congrFun hfull i.castSucc

theorem evaluation (P : MvPolynomial (Fin 4) F) (v : Fin 3 → F) :
    eval (Fin.cons 1 (point v)) (rename permutation P) = eval (Fin.snoc v 1) P := by
  rw [full_point]
  exact CoordinateSwapEvaluation.evaluation P (Fin.snoc v 1) 0 3

theorem evaluation_partial (P : MvPolynomial (Fin 4) F) (v : Fin 3 → F) (k : Fin 4) :
    eval (Fin.cons 1 (point v)) (pderiv (permutation k) (rename permutation P)) =
      eval (Fin.snoc v 1) (pderiv k P) := by
  rw [pderiv_rename permutation.injective k P, evaluation]

theorem free_gradient (P : MvPolynomial (Fin 4) F) {d : ℕ} (hP : P.IsHomogeneous d)
    (a : Fin 3 → F) (hroot : eval (Fin.cons 1 a) P = 0)
    (hgrad : ∃ k : Fin 4, eval (Fin.cons 1 a) (pderiv k P) ≠ 0) :
    ∃ i : Fin 3, eval (Fin.cons 1 a) (pderiv i.succ P) ≠ 0 := by
  by_contra hn
  have hz : ∀ i : Fin 3, eval (Fin.cons 1 a) (pderiv i.succ P) = 0 := by
    intro i
    exact Classical.not_not.mp (fun h ↦ hn ⟨i, h⟩)
  have he := congrArg (eval (Fin.cons 1 a)) hP.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at he
  rw [Fin.sum_univ_succ, Fin.cons_zero, one_mul] at he
  have hfirst : eval (Fin.cons 1 a) (pderiv (0 : Fin 4) P) = 0 := by
    simpa only [hz, mul_zero, Finset.sum_const_zero, add_zero, hroot, mul_zero] using he
  obtain ⟨k, hk⟩ := hgrad
  cases k using Fin.cases with
  | zero => exact hk hfirst
  | succ k => exact hk (hz k)

end PaperP1.P3FieldChartExchange
