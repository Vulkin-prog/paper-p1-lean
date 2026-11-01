module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # The finite modulus-product cost in moderate certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateModuli

open Finset

variable {ι : Type*} [Fintype ι]

def large (N : ℕ) (D : ι → ℕ) : Finset ι := univ.filter fun i ↦ N < D i

theorem large_card_le_two (N : ℕ) (hN : 10 ≤ N) (D : ι → ℕ)
    (hD : ∀ i, 1 ≤ D i) (hprod : (∏ i, D i) ≤ 9 * N ^ 2) : (large N D).card ≤ 2 := by
  by_contra hcard
  have hthree : 3 ≤ (large N D).card := by omega
  have hpow : (N + 1) ^ (large N D).card ≤ ∏ i ∈ large N D, D i := by
    apply pow_card_le_prod
    intro i hi
    have h := (mem_filter.mp hi).2
    omega
  have hsub : (∏ i ∈ large N D, D i) ≤ ∏ i, D i :=
    prod_le_prod_of_subset_of_one_le (filter_subset _ _) (fun i _ _ ↦ hD i)
  have hpowthree : (N + 1) ^ 3 ≤ (N + 1) ^ (large N D).card :=
    Nat.pow_le_pow_right (by omega) hthree
  have hNpos : 0 < N ^ 2 := pow_pos (by omega) 2
  have hcube : 9 * N ^ 2 < (N + 1) ^ 3 := by
    have h := Nat.mul_lt_mul_of_pos_right (by omega : 9 < N) hNpos
    nlinarith
  exact (not_lt_of_ge (hpowthree.trans (hpow.trans (hsub.trans hprod)))) hcube

theorem one_add_div_le (N D : ℕ) (hD : 1 ≤ D) (A : ℝ) (hA : 1 ≤ A)
    (hupper : (D : ℝ) ≤ A * N) :
    1 + (N : ℝ) / D ≤ (if N < D then A else 1) * (2 * (N : ℝ) / D) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hDpos).mpr
  rw [add_mul, one_mul, div_mul_cancel₀ _ hDpos.ne']
  by_cases hND : N < D
  · rw [ite_eq_left hND]
    have hNA : (N : ℝ) ≤ A * N := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg N)
    nlinarith
  · rw [ite_eq_right hND]
    have hDN : (D : ℝ) ≤ N := by exact_mod_cast (by omega : D ≤ N)
    linarith

theorem product_cost_le (N : ℕ) (hN : 10 ≤ N) (D : ι → ℕ)
    (hD : ∀ i, 1 ≤ D i) (hprod : (∏ i, D i) ≤ 9 * N ^ 2)
    (A : ℝ) (hA : 1 ≤ A) (hupper : ∀ i, (D i : ℝ) ≤ A * N) :
    (∏ i, (1 + (N : ℝ) / D i)) ≤
      A ^ 2 * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ) := by
  have hcoefficient : (∏ i, (if N < D i then A else 1)) = A ^ (large N D).card := by
    rw [prod_ite]
    simp only [large, prod_const, one_pow, mul_one]
  have hcost : (∏ i, (2 * (N : ℝ) / D i)) =
      2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ) := by
    rw [prod_div_distrib, prod_const, card_univ, mul_pow, Nat.cast_prod]
  have hnonneg : 0 ≤ 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ) := by positivity
  calc
    _ ≤ ∏ i, ((if N < D i then A else 1) * (2 * (N : ℝ) / D i)) := by
      apply prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact one_add_div_le N (D i) (hD i) A hA (hupper i)
    _ = (∏ i, (if N < D i then A else 1)) * ∏ i, (2 * (N : ℝ) / D i) := prod_mul_distrib
    _ = A ^ (large N D).card *
        (2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ)) := by rw [hcoefficient, hcost]
    _ ≤ A ^ 2 * (2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA (large_card_le_two N hN D hD hprod)) hnonneg
    _ = _ := by ring

end PaperP1.ModerateModuli
