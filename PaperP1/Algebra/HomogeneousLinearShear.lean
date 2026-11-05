/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Copyright (c) 2026 the paper-p1-lean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Johan Commelin, Eric Wieser.
The top-coefficient argument follows the homogeneous finSuccEquiv argument in
Mathlib/RingTheory/MvPolynomial/Homogeneous.lean at
9d581dfff2e41de989072ea63abf3daf69311520.
-/
module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.Algebra.MvPolynomial.Monad
public import Lean.Elab.Tactic.Omega

/-! # Linear coordinate shears preserving homogeneous degrees

Over an infinite field, a nonzero homogeneous equation can be made to have
invertible leading coefficient in the first variable by a linear shear.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousLinearShear

open MvPolynomial

variable {F : Type*} [CommRing F] {n e : ℕ}

local instance polynomialRing : CommRing (MvPolynomial (Fin (n + 1)) F) := inferInstance

theorem top_coefficient (p : MvPolynomial (Fin (n + 1)) F) (hp : p.IsHomogeneous e) :
    (finSuccEquiv F n p).coeff e = C (eval (Fin.cons 1 0) p) := by
  have hdeg : (finSuccEquiv F n p).natDegree < e + 1 := by
    rw [natDegree_finSuccEquiv]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree p 0).trans hp.totalDegree_le)
  have aux : ∀ i ∈ Finset.range e, constantCoeff ((finSuccEquiv F n p).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hp.finSuccEquiv_coeff_isHomogeneous i (e - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    exact (Nat.sub_ne_zero_of_lt hi).symm
  have he : eval (Fin.cons 1 0) p = constantCoeff ((finSuccEquiv F n p).coeff e) := by
    simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
      Polynomial.eval_eq_sum_range' hdeg, eval_zero, one_pow, mul_one,
      map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  rw [he]
  exact HomogeneousPolynomialEvaluation.homogeneous_zero_eq_C _
    (hp.finSuccEquiv_coeff_isHomogeneous e 0 (Nat.add_zero e))

def substitute (v : Fin n → F) : MvPolynomial (Fin (n + 1)) F →ₐ[F] MvPolynomial (Fin (n + 1)) F :=
  aeval (Fin.cons (X 0) (fun i ↦ X i.succ + C (v i) * X 0))

theorem substitute_zero : substitute (0 : Fin n → F) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [substitute]

theorem substitute_add (v w : Fin n → F) :
    (substitute v).comp (substitute w) = substitute (v + w) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [substitute]
  | succ i => simp [substitute, map_add, map_mul]; ring

def equiv (v : Fin n → F) : MvPolynomial (Fin (n + 1)) F ≃ₐ[F] MvPolynomial (Fin (n + 1)) F :=
  AlgEquiv.ofAlgHom (substitute v) (substitute (-v))
    (by rw [substitute_add, add_neg_cancel, substitute_zero])
    (by rw [substitute_add, neg_add_cancel, substitute_zero])

theorem homogeneous (v : Fin n → F) (p : MvPolynomial (Fin (n + 1)) F) (hp : p.IsHomogeneous e) :
    (substitute v p).IsHomogeneous e := by
  have hv (i : Fin (n + 1)) :
      ((Fin.cons (α := fun _ ↦ MvPolynomial (Fin (n + 1)) F) (X 0)
        (fun j ↦ X j.succ + C (v j) * X 0)) i : MvPolynomial (Fin (n + 1)) F).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero => exact isHomogeneous_X F 0
    | succ i => exact (isHomogeneous_X F i.succ).add (isHomogeneous_C_mul_X _ 0)
  simpa only [substitute, one_mul] using! hp.aeval _ hv

theorem eval_substitute (v : Fin n → F) (p : MvPolynomial (Fin (n + 1)) F) :
    eval (Fin.cons 1 0) (substitute v p) = eval (Fin.cons 1 v) p := by
  have he : (aeval (Fin.cons 1 0)).comp (substitute v) = aeval (Fin.cons 1 v) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;> simp [substitute]
  exact DFunLike.congr_fun he p

theorem exists_unit_leadingCoeff {F : Type*} [Field F] [Infinite F]
    (p : MvPolynomial (Fin (n + 1)) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) :
    ∃ v : Fin n → F, IsUnit (finSuccEquiv F n (substitute v p)).leadingCoeff := by
  obtain ⟨v, hv⟩ := HomogeneousPolynomialEvaluation.exists_eval_cons_one p hp hp0
  have ht := top_coefficient (substitute v p) (homogeneous v p hp)
  rw [eval_substitute] at ht
  have ht0 : (finSuccEquiv F n (substitute v p)).coeff e ≠ 0 := by
    rw [ht]
    exact C_ne_zero.mpr hv
  have hdeg : (finSuccEquiv F n (substitute v p)).natDegree = e := by
    apply le_antisymm
    · rw [natDegree_finSuccEquiv]
      exact (degreeOf_le_totalDegree _ 0).trans (homogeneous v p hp).totalDegree_le
    · exact Polynomial.le_natDegree_of_ne_zero ht0
  refine ⟨v, ?_⟩
  rw [Polynomial.leadingCoeff, hdeg, ht]
  exact hv.isUnit.map C

end PaperP1.HomogeneousLinearShear
