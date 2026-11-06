module

public import PaperP1.Algebra.HomogeneousLinearForm
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Actual triangular linear changes of the first polynomial coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstCoordinateShear

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [CommRing F] {n : ℕ}

def form (b : Fin n → F) : MvPolynomial (Fin (n + 1)) F :=
  ∑ i, C (b i) * X i.succ

def substitute (b : Fin n → F) :
    MvPolynomial (Fin (n + 1)) F →ₐ[F] MvPolynomial (Fin (n + 1)) F :=
  aeval (Fin.cons (X 0 + form b) (fun i ↦ X i.succ))

theorem substitute_X_zero (b : Fin n → F) : substitute b (X 0) = X 0 + form b := by
  simp [substitute]

theorem substitute_X_succ (b : Fin n → F) (i : Fin n) : substitute b (X i.succ) = X i.succ := by
  simp [substitute]

theorem substitute_form (b c : Fin n → F) : substitute b (form c) = form c := by
  simp [form, map_sum, map_mul, substitute_X_succ]

theorem form_add (b c : Fin n → F) : form (b + c) = form b + form c := by
  simp only [form, Pi.add_apply, map_add, add_mul, sum_add_distrib]

theorem substitute_zero : substitute (0 : Fin n → F) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [substitute, form]

theorem substitute_add (b c : Fin n → F) :
    (substitute b).comp (substitute c) = substitute (b + c) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero =>
    simp only [AlgHom.comp_apply, substitute_X_zero, map_add, substitute_form, form_add]
    ring
  | succ i => simp only [AlgHom.comp_apply, substitute_X_succ]

def equiv (b : Fin n → F) : MvPolynomial (Fin (n + 1)) F ≃ₐ[F] MvPolynomial (Fin (n + 1)) F :=
  AlgEquiv.ofAlgHom (substitute b) (substitute (-b))
    (by rw [substitute_add, add_neg_cancel, substitute_zero])
    (by rw [substitute_add, neg_add_cancel, substitute_zero])

theorem homogeneous (b : Fin n → F) (P : MvPolynomial (Fin (n + 1)) F) {d : ℕ}
    (hP : P.IsHomogeneous d) : (substitute b P).IsHomogeneous d := by
  have hf : (form b).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact (isHomogeneous_X F i.succ).C_mul (b i)
  have hY : ∀ i : Fin (n + 1),
      ((Fin.cons (X 0 + form b) (fun j ↦ X j.succ) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) F) i).IsHomogeneous 1 := by
    intro i
    cases i using Fin.cases with
    | zero => exact (isHomogeneous_X F 0).add hf
    | succ i => exact isHomogeneous_X F i.succ
  simpa only [substitute, one_mul] using hP.aeval _ hY

def point (b : Fin n → F) (v : Fin (n + 1) → F) : Fin (n + 1) → F :=
  Fin.cons (v 0 + ∑ i, b i * v i.succ) (Fin.tail v)

theorem evaluation (b : Fin n → F) (P : MvPolynomial (Fin (n + 1)) F)
    (v : Fin (n + 1) → F) : eval v (substitute b P) = eval (point b v) P := by
  have he : (eval v).comp (substitute b).toRingHom = eval (point b v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [substitute]
    · intro i
      cases i using Fin.cases <;> simp [substitute, point, form, Fin.tail]
  exact RingHom.congr_fun he P

theorem point_add (b c : Fin n → F) (v : Fin (n + 1) → F) :
    point b (point c v) = point (b + c) v := by
  funext i
  cases i using Fin.cases with
  | zero => simp [point, Fin.tail, sum_add_distrib, add_mul]; ring
  | succ i => rfl

theorem point_injective (b : Fin n → F) : Function.Injective (point b) := by
  intro v w he
  have hh := congrArg (point (-b)) he
  rw [point_add, point_add, neg_add_cancel] at hh
  have hzero (u : Fin (n + 1) → F) : point (0 : Fin n → F) u = u := by
    simp only [point, Pi.zero_apply, zero_mul, sum_const_zero, add_zero, Fin.cons_self_tail]
  simpa only [hzero] using hh

end PaperP1.FirstCoordinateShear
