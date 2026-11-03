module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Fintype.Perm

/-! # Coprime row congruences force small replacement determinants to vanish

This is the finite determinant step of companion T8.1. The divisors may be
composite. The replacement row has its own height, so its large coordinates
are paid for only once in the determinant estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoprimeRowDeterminants

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem row_dvd (A : Matrix ι ι ℤ) (r : ι) (g : ℤ)
    (hrow : ∀ j, g ∣ A r j) : g ∣ A.det := by
  rw [← det_transpose, det_apply']
  apply dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  exact (hrow (σ r)).trans (dvd_prod_of_mem (fun i ↦ Aᵀ (σ i) i) (mem_univ r))

theorem difference_row_dvd (A : Matrix ι ι ℤ) (r k : ι) (hkr : k ≠ r) (g : ℤ)
    (hrow : ∀ j, g ∣ A k j - A r j) : g ∣ A.det := by
  have hdet : (A.updateRow k (A k - A r)).det = A.det := by
    simpa only [neg_one_smul, sub_eq_add_neg] using
      det_updateRow_add_smul_self A hkr (-1 : ℤ)
  rw [← hdet]
  apply row_dvd _ k g
  intro j
  simpa only [updateRow_self, Pi.sub_apply] using hrow j

theorem replacement_product_dvd (A : Matrix ι ι ℤ) (v : ι → ℤ) (r : ι) (g : ι → ℕ)
    (hcop : Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hrow : ∀ i j, (g i : ℤ) ∣ A i j - v j) :
    (∏ i ∈ univ.erase r, g i) ∣ (A.updateRow r v).det.natAbs := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact Nat.coprime_iff_isRelPrime.mp (hcop hij)
  · intro i hi
    have hir : i ≠ r := (mem_erase.mp hi).1
    apply Int.natCast_dvd.mp
    apply difference_row_dvd _ r i hir
    intro j
    simpa only [updateRow_ne hir, updateRow_self] using hrow i j

theorem replacement_height (A : Matrix ι ι ℤ) (v : ι → ℤ) (r : ι) (U V : ℕ)
    (hU : ∀ j, (v j).natAbs ≤ U) (hV : ∀ i j, (A i j).natAbs ≤ V) :
    (A.updateRow r v).det.natAbs ≤
      (Fintype.card ι).factorial * U * V ^ (Fintype.card ι - 1) := by
  rw [← det_transpose, det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) * ∏ i, (A.updateRow r v)ᵀ (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ((A.updateRow r v) i (σ i)).natAbs := by
      apply sum_congr rfl
      intro σ _
      rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
      exact map_prod Int.natAbsHom _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, U * V ^ (Fintype.card ι - 1) := by
      apply sum_le_sum
      intro σ _
      rw [← mul_prod_erase univ (fun i ↦ ((A.updateRow r v) i (σ i)).natAbs) (mem_univ r)]
      apply Nat.mul_le_mul
      · simpa only [updateRow_self] using hU (σ r)
      · calc
          _ ≤ ∏ _i ∈ univ.erase r, V := by
            apply prod_le_prod
            intro i hi
            rw [updateRow_ne (mem_erase.mp hi).1]
            exact hV i (σ i)
          _ = V ^ (Fintype.card ι - 1) := by simp
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_perm, Nat.cast_id]; ring

theorem replacement_zero (A : Matrix ι ι ℤ) (v : ι → ℤ) (r : ι) (g : ι → ℕ)
    (hcop : Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hrow : ∀ i j, (g i : ℤ) ∣ A i j - v j) (U V : ℕ)
    (hU : ∀ j, (v j).natAbs ≤ U) (hV : ∀ i j, (A i j).natAbs ≤ V)
    (hlarge : (Fintype.card ι).factorial * U * V ^ (Fintype.card ι - 1) <
      ∏ i ∈ univ.erase r, g i) : (A.updateRow r v).det = 0 := by
  by_contra hne
  have hdiv := replacement_product_dvd A v r g hcop hrow
  have hlo := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdiv
  have hhi := replacement_height A v r U V hU hV
  omega

theorem determinant_zero_of_replacements (A : Matrix ι ι ℤ) (v : ι → ℤ) (c : ι)
    (hc : v c = 1) (hzero : ∀ r, (A.updateRow r v).det = 0) : A.det = 0 := by
  have hcramer : Aᵀ.cramer v = 0 := by
    funext r
    rw [cramer_transpose_apply, hzero r, Pi.zero_apply]
  have he := congrFun (mulVec_cramer Aᵀ v) c
  simpa only [hcramer, mulVec_zero, Pi.zero_apply, Pi.smul_apply,
    smul_eq_mul, det_transpose, hc, mul_one] using he.symm

end PaperP1.CoprimeRowDeterminants
