module

public import PaperP1.Model.RegularAffineBounds
public import PaperP1.Model.CountObservables

/-! # Finite regular-set transfer with exact constants

The only rank hypothesis is the already proved critical-window bound r ≤ 1.
The original count and its restriction use the same infinite prime signs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularSetFinite

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Probability RegularStarts RegularAffineBounds CountObservables WindowRelationCode Finset

local instance regularSetFinitePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem card_dyadicBlock (N : ℕ) : (dyadicBlock N).card = N := by
  simp only [dyadicBlock, Nat.card_Ico, two_mul, Nat.add_sub_cancel_left]

theorem card_irregular_add_regular (N L : ℕ) :
    (irregularStarts N L).card + (regularStarts N L).card = N := by
  simpa only [irregularStarts, card_dyadicBlock] using
    card_sdiff_add_card_eq_card (regularStarts_subset N L)

theorem mean_regular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    countMoment (regularStarts N L) L 1 = (2 ^ L : ℝ)⁻¹ * (regularStarts N L).card := by
  rw [countMoment_one (regularStarts_subset N L)]
  calc
    _ = ∑ _x ∈ regularStarts N L, (2 ^ L : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro x hx
      have hxpos : 0 < x := by
        have := (mem_Ico.mp ((regularStarts_subset N L) hx)).1
        omega
      exact marginal_on_regular hxpos hL hx
    _ = _ := by simp [mul_comm]

theorem regular_mean_bias {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    |countMoment (regularStarts N L) L 1 - N * (2 ^ L : ℝ)⁻¹| =
      (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
  have hcard : ((irregularStarts N L).card : ℝ) + (regularStarts N L).card = N := by
    exact_mod_cast card_irregular_add_regular N L
  have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos (by norm_num) _))
  rw [mean_regular hN hL]
  have heq : (2 ^ L : ℝ)⁻¹ * (regularStarts N L).card - N * (2 ^ L : ℝ)⁻¹ =
      -((2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card) := by rw [← hcard]; ring
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg hp (Nat.cast_nonneg _))]

theorem full_mean_bias {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hr : ∀ x ∈ dyadicBlock N,
      Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹| ≤
      (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
  have h := sum_affine_deviations_le hN hL hr (dyadicBlock N) (subset_refl _)
    (fun _ ↦ startRhs L)
  have heq : countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ =
      ∑ x ∈ dyadicBlock N, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹) := by
    rw [countMoment_one (subset_refl _), sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, card_dyadicBlock]
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  simpa only [affineWindowMass, infiniteMarginal_eq_affine_atom hL] using h

theorem discarded_activity_le {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hr : ∀ x ∈ dyadicBlock N,
      Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    countDisagreement (dyadicBlock N) (regularStarts N L) L ≤
      2 * (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
  calc
    _ ≤ ∑ x ∈ irregularStarts N L, infiniteMarginal x L :=
      countDisagreement_subset_le (subset_refl _) (regularStarts_subset N L)
    _ ≤ ∑ _x ∈ irregularStarts N L, 2 * (2 ^ L : ℝ)⁻¹ := by
      apply sum_le_sum
      intro x hx
      have hxblock := (mem_irregularStarts.mp hx).1
      have hxpos : 0 < x := by have := (mem_Ico.mp hxblock).1; omega
      have h := affineWindowMass_le_twice_nominal hxpos hL (hr x hxblock) (startRhs L)
      simpa only [affineWindowMass, infiniteMarginal_eq_affine_atom hL] using h
    _ = _ := by simp [mul_comm]

theorem regular_set_finite_transfer {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hr : ∀ x ∈ dyadicBlock N,
      Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    lawTotalVariation (dyadicCountLaw N L) (restrictedCountLaw N L (regularStarts N L)) +
      |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹| +
      |countMoment (regularStarts N L) L 1 - N * (2 ^ L : ℝ)⁻¹| ≤
        4 * (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card := by
  have htv := (count_law_subset_coupling (N := N) (L := L) (subset_refl _)
    (regularStarts_subset N L)).trans (discarded_activity_le hN hL hr)
  have hfull := full_mean_bias hN hL hr
  have hreg := regular_mean_bias hN hL
  change lawTotalVariation (dyadicCountLaw N L) _ ≤ _ at htv
  linarith

end PaperP1.RegularSetFinite
