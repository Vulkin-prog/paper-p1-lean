module

public import PaperP1.Algebra.FormalWordPolynomials
public import PaperP1.Algebra.BivariateDegrees

/-! # Exact partial degrees and half-rank balance for the formal-word overlap quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalWordDegrees

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.BivariateDegrees
open scoped symmDiff

theorem linear_monic (R : Type*) [CommRing R] (I : Finset ℤ) : (linearOver R I).Monic :=
  monic_prod_of_monic _ _ (fun i _ ↦ monic_X_add_C (i : R))

theorem linear_degree (R : Type*) [CommRing R] [Nontrivial R] (I : Finset ℤ) :
    (linearOver R I).natDegree = I.card := by
  rw [linearOver, natDegree_prod_of_monic I (fun i : ℤ ↦ (X : R[X]) + C (i : R))
    (fun i _ ↦ monic_X_add_C (i : R))]
  simp only [natDegree_X_add_C, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem word_degreeY (I J : Finset ℤ) : degreeY (wordOver ℤ I J) = J.card := by
  have hp : linearOver ℤ I ≠ 0 := (linear_monic ℤ I).ne_zero
  have hq : (linearOver ℤ J).map C ≠ 0 :=
    (Polynomial.map_ne_zero_iff C_injective).mpr (linear_monic ℤ J).ne_zero
  change (C (linearOver ℤ I) * (linearOver ℤ J).map C).natDegree = J.card
  rw [natDegree_mul (C_ne_zero.mpr hp) hq, natDegree_C,
    natDegree_map_eq_of_injective C_injective, linear_degree, zero_add]

theorem word_swap (R : Type*) [CommRing R] (I J : Finset ℤ) :
    Bivariate.swap (wordOver R I J) = wordOver R J I := by
  simp only [wordOver, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, mul_comm]

theorem word_degreeX (I J : Finset ℤ) : degreeX (wordOver ℤ I J) = I.card := by
  rw [degreeX, word_swap]
  exact word_degreeY J I

theorem quotient_rank_balance (I K : Finset ℤ) (r₁ r₂ r₃ : ℕ)
    (hI : I.card = 2 * r₁) (hK : K.card = 2 * r₂) (hx : (I ∆ K).card = 2 * r₃) :
    (K \ I).card + r₁ = r₂ + r₃ := by
  have h₁ := card_sdiff_add_card_inter I K
  have h₂ := card_sdiff_add_card_inter K I
  have hd : Disjoint (I \ K) (K \ I) := by
    apply disjoint_left.mpr
    intro i hi hk
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hk).1
  have hxor : (I ∆ K).card = (I \ K).card + (K \ I).card := by
    rw [Finset.symmDiff_def, card_union_of_disjoint hd]
  rw [inter_comm K I] at h₂
  omega

end PaperP1.FormalWordDegrees
