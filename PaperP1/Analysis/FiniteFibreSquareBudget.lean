module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Exact square-norm control under actual finite coefficient aggregation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFibreSquareBudget
open Finset
open scoped Classical

def aggregate {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) (a : α → ℂ) (b : β) : ℂ :=
  ∑ x ∈ S.filter (fun x ↦ f x = b), a x

theorem norm_sum_sq_le_card {α : Type*} (S : Finset α) (a : α → ℂ) :
    ‖∑ x ∈ S, a x‖^2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖a x‖^2 := by
  have hn := norm_sum_le S a
  have hs : 0 ≤ ∑ x ∈ S, ‖a x‖ := sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hh := sum_mul_sq_le_sq_mul_sq S (fun _ : α ↦ (1 : ℝ)) (fun x ↦ ‖a x‖)
  have hc : (∑ x ∈ S, ‖a x‖)^2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖a x‖^2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using hh
  exact (show ‖∑ x ∈ S, a x‖^2 ≤ (∑ x ∈ S, ‖a x‖)^2 by nlinarith [norm_nonneg (∑ x ∈ S, a x)]).trans hc

theorem aggregate_square_budget {α β : Type*} [DecidableEq β] (S : Finset α)
    (f : α → β) (a : α → ℂ) (B : ℕ)
    (hB : ∀ b ∈ S.image f, (S.filter fun x ↦ f x = b).card ≤ B) :
    (∑ b ∈ S.image f, ‖aggregate S f a b‖^2) ≤ (B : ℝ) * ∑ x ∈ S, ‖a x‖^2 := by
  have hpoint : ∀ b ∈ S.image f, ‖aggregate S f a b‖^2 ≤
      (B : ℝ) * ∑ x ∈ S.filter (fun x ↦ f x = b), ‖a x‖^2 := by
    intro b hb
    change ‖∑ x ∈ S.filter (fun x ↦ f x = b), a x‖^2 ≤ _
    have hcard : ((S.filter (fun x ↦ f x = b)).card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB b hb
    exact (norm_sum_sq_le_card (S.filter (fun x ↦ f x = b)) a).trans
      (mul_le_mul_of_nonneg_right hcard (sum_nonneg (fun _ _ ↦ sq_nonneg _)))
  have hmap : Set.MapsTo f S (S.image f) := fun x hx ↦ mem_image_of_mem f hx
  have he := sum_fiberwise_of_maps_to hmap (fun x ↦ ‖a x‖^2)
  calc
    _ ≤ ∑ b ∈ S.image f, (B : ℝ) * ∑ x ∈ S.filter (fun x ↦ f x = b), ‖a x‖^2 := sum_le_sum hpoint
    _ = (B : ℝ) * (∑ b ∈ S.image f, ∑ x ∈ S.filter (fun x ↦ f x = b), ‖a x‖^2) := by rw [mul_sum]
    _ = _ := by rw [he]
end FiniteFibreSquareBudget
