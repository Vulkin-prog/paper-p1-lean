module

public import PaperP1.Analysis.ReciprocalSqrtSum
public import Mathlib.Data.Finset.Max

/-! # Finite inverse-square tail counts control the full first-moment sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSquareTail

open Finset

theorem sum_bound {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ x ∈ S, 0 ≤ f x)
    (htail : ∀ L : ℝ, 0 < L → ((S.filter (fun x ↦ L ≤ f x)).card : ℝ) * L ^ 2 ≤ C) :
    (∑ x ∈ S, f x) ≤ 2 * Real.sqrt C * Real.sqrt S.card := by
  classical
  revert hf htail
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hf htail
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨x, hx, hmin⟩ := exists_min_image S f hne
    have hsmall := ih (S.erase x) (erase_ssubset hx)
      (fun y hy ↦ hf y (mem_erase.mp hy).2) (by
        intro L hL
        have hsub : (S.erase x).filter (fun y ↦ L ≤ f y) ⊆ S.filter (fun y ↦ L ≤ f y) := by
          intro y hy
          obtain ⟨hyS, hyL⟩ := mem_filter.mp hy
          exact mem_filter.mpr ⟨(mem_erase.mp hyS).2, hyL⟩
        have hcard : (((S.erase x).filter (fun y ↦ L ≤ f y)).card : ℝ) ≤
            ((S.filter (fun y ↦ L ≤ f y)).card : ℝ) := by exact_mod_cast card_le_card hsub
        exact (mul_le_mul_of_nonneg_right hcard (sq_nonneg L)).trans (htail L hL))
    have hfilter : S.filter (fun y ↦ f x ≤ f y) = S := filter_eq_self.mpr hmin
    have hminimum : (S.card : ℝ) * f x ^ 2 ≤ C := by
      by_cases hpos : 0 < f x
      · simpa only [hfilter] using htail (f x) hpos
      · have hz : f x = 0 := le_antisymm (le_of_not_gt hpos) (hf x hx)
        simpa only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hC
    have hcardNat : 1 ≤ S.card := card_pos.mpr hne
    have hroot : 0 < Real.sqrt S.card := Real.sqrt_pos.mpr (by exact_mod_cast hcardNat)
    have hsquare : (f x * Real.sqrt S.card) ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg S.card), Real.sq_sqrt hC]
      nlinarith only [hminimum]
    have hproduct : f x * Real.sqrt S.card ≤ Real.sqrt C :=
      (sq_le_sq₀ (mul_nonneg (hf x hx) hroot.le) (Real.sqrt_nonneg C)).mp hsquare
    have hterm : f x ≤ Real.sqrt C / Real.sqrt S.card := (le_div_iff₀ hroot).mpr hproduct
    rw [div_eq_mul_inv] at hterm
    have hstep := PaperP1.inv_sqrt_nat_le_two_mul_sqrt_sub S.card hcardNat
    have hlast := hterm.trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg C))
    rw [card_erase_of_mem hx] at hsmall
    have hsum := sum_erase_add S f hx
    nlinarith only [hlast, hsmall, hsum]

theorem sum_bound_of_div_tail {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ x ∈ S, 0 ≤ f x)
    (htail : ∀ L : ℝ, 0 < L → ((S.filter (fun x ↦ L ≤ f x)).card : ℝ) ≤ C / L ^ 2) :
    (∑ x ∈ S, f x) ≤ 2 * Real.sqrt C * Real.sqrt S.card := by
  apply sum_bound S f C hC hf
  intro L hL
  exact (le_div_iff₀ (sq_pos_of_pos hL)).mp (htail L hL)

end PaperP1.FiniteSquareTail
