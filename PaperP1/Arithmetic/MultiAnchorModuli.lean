module

public import PaperP1.Arithmetic.ModerateModuli

/-! # Moderate receiving moduli for products of t anchor kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorModuli

open Finset PaperP1.ModerateModuli

variable {ι : Type*} [Fintype ι]

theorem large_card_le (t N : ℕ) (hN : 3 ^ t < N) (D : ι → ℕ)
    (hD : ∀ i, 1 ≤ D i) (hprod : (∏ i, D i) ≤ (3 * N) ^ t) :
    (large N D).card ≤ t := by
  by_contra hcard
  have hnext : t + 1 ≤ (large N D).card := by omega
  have hpow : (N + 1) ^ (large N D).card ≤ ∏ i ∈ large N D, D i := by
    apply pow_card_le_prod
    intro i hi
    have h := (mem_filter.mp hi).2
    omega
  have hsub : (∏ i ∈ large N D, D i) ≤ ∏ i, D i :=
    prod_le_prod_of_subset_of_one_le (filter_subset _ _) (fun i _ _ ↦ hD i)
  have hpowNext : (N + 1) ^ (t + 1) ≤ (N + 1) ^ (large N D).card :=
    Nat.pow_le_pow_right (by omega) hnext
  have hNpos : 0 < N := lt_trans (pow_pos (by omega : 0 < (3 : ℕ)) t) hN
  have hstrict : (3 * N) ^ t < (N + 1) ^ (t + 1) := by
    calc
      _ = 3 ^ t * N ^ t := Nat.mul_pow _ _ _
      _ < N * N ^ t := Nat.mul_lt_mul_of_pos_right hN (pow_pos hNpos t)
      _ = N ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ (N + 1) ^ (t + 1) := Nat.pow_le_pow_left (by omega) _
  exact (not_lt_of_ge (hpowNext.trans (hpow.trans (hsub.trans hprod)))) hstrict

theorem product_cost_le (t N : ℕ) (hN : 3 ^ t < N) (D : ι → ℕ)
    (hD : ∀ i, 1 ≤ D i) (hprod : (∏ i, D i) ≤ (3 * N) ^ t)
    (A : ℝ) (hA : 1 ≤ A) (hupper : ∀ i, (D i : ℝ) ≤ A * N) :
    (∏ i, (1 + (N : ℝ) / D i)) ≤
      A ^ t * 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
        (↑(∏ i, D i) : ℝ) := by
  have hcoefficient : (∏ i, (if N < D i then A else 1)) = A ^ (large N D).card := by
    rw [prod_ite]
    simp only [large, prod_const, one_pow, mul_one]
  have hcost : (∏ i, (2 * (N : ℝ) / D i)) =
      2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ) := by
    rw [prod_div_distrib, prod_const, card_univ, mul_pow, Nat.cast_prod]
  have hnonneg : 0 ≤ 2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι /
      (↑(∏ i, D i) : ℝ) := by positivity
  calc
    _ ≤ ∏ i, ((if N < D i then A else 1) * (2 * (N : ℝ) / D i)) := by
      apply prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact one_add_div_le N (D i) (hD i) A hA (hupper i)
    _ = (∏ i, (if N < D i then A else 1)) * ∏ i, (2 * (N : ℝ) / D i) :=
      prod_mul_distrib
    _ = A ^ (large N D).card *
        (2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ)) := by
      rw [hcoefficient, hcost]
    _ ≤ A ^ t *
        (2 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι / (↑(∏ i, D i) : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA (large_card_le t N hN D hD hprod)) hnonneg
    _ = _ := by ring

end PaperP1.MultiAnchorModuli
