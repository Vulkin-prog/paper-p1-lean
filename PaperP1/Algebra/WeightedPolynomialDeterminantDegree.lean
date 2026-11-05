module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # Polynomial determinant degrees with exact row and column shifts

Only nonzero entries need to satisfy the shifted degree constraints. The zero
product cases are handled explicitly, so arbitrary commutative coefficient
rings are allowed. This supplies the sharp Sylvester degree budget.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPolynomialDeterminantDegree

open Polynomial Finset

variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem product_degree (f : ι → R[X]) (r c : ι → ℤ) (T : ℕ)
    (hbudget : (∑ i, c i) ≤ (T : ℤ) + ∑ i, r i)
    (hdeg : ∀ i, f i ≠ 0 → ((f i).natDegree : ℤ) + r i ≤ c i) :
    (∏ i, f i).natDegree ≤ T := by
  classical
  by_cases hz : (∏ i, f i) = 0
  · rw [hz, natDegree_zero]
    exact Nat.zero_le T
  · have hf : ∀ i, f i ≠ 0 := by
      intro i hi
      exact hz (Finset.prod_eq_zero (mem_univ i) hi)
    have hs := Finset.sum_le_sum (fun i (_hi : i ∈ (univ : Finset ι)) ↦ hdeg i (hf i))
    rw [Finset.sum_add_distrib] at hs
    have ht : (∑ i, ((f i).natDegree : ℤ)) ≤ (T : ℤ) := by omega
    have htn : (∑ i, (f i).natDegree) ≤ T := by exact_mod_cast ht
    exact (Polynomial.natDegree_prod_le _ _).trans htn

variable [DecidableEq ι]

theorem determinant_degree (M : Matrix ι ι R[X]) (r c : ι → ℤ) (T : ℕ)
    (hbudget : (∑ j, c j) ≤ (T : ℤ) + ∑ i, r i)
    (hdeg : ∀ i j, M i j ≠ 0 → ((M i j).natDegree : ℤ) + r i ≤ c j) :
    M.det.natDegree ≤ T := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _hσ
  have hperm : (∑ i, r (σ i)) = ∑ i, r i := Equiv.sum_comp σ r
  have hp := product_degree (fun i ↦ M (σ i) i) (fun i ↦ r (σ i)) c T
    (by simpa only [hperm] using hbudget) (fun i hi ↦ hdeg (σ i) i hi)
  have hm := Polynomial.natDegree_mul_le
    (p := ((Equiv.Perm.sign σ : ℤ) : R[X])) (q := ∏ i, M (σ i) i)
  exact hm.trans (by simpa only [natDegree_intCast, zero_add] using hp)

end PaperP1.WeightedPolynomialDeterminantDegree
