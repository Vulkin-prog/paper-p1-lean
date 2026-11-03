module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp

/-! # A pointwise power-mean bound and its finite first-moment consequence, uniform in the number of positions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteProductPowerMean

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem product_le_average_power (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∏ i, f i) ≤ (∑ i, f i ^ Fintype.card ι) / (Fintype.card ι : ℝ) := by
  classical
  let B := Fintype.card ι
  have hB : (0 : ℝ) < B := by dsimp [B]; exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : ι, 1 / (B : ℝ)) = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    change (B : ℝ) * (1 / B) = 1
    field_simp
  have h := Real.geom_mean_le_arith_mean_weighted univ (fun _ : ι ↦ 1 / (B : ℝ))
    (fun i ↦ f i ^ B) (fun _ _ ↦ by positivity) hw (fun i _ ↦ pow_nonneg (hf i) _)
  have heq (i : ι) : (f i ^ B) ^ (1 / (B : ℝ)) = f i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hf i)]
    rw [show (B : ℝ) * (1 / B) = 1 by field_simp, Real.rpow_one]
  simp_rw [heq] at h
  calc
    _ ≤ ∑ i : ι, (1 / (B : ℝ)) * f i ^ B := h
    _ = _ := by rw [← mul_sum]; dsimp [B]; ring

theorem sum_product_le_moment {α : Type*} (X : Finset α) (f : ι → α → ℝ)
    (hf : ∀ i, ∀ x ∈ X, 0 ≤ f i x) (K : ℝ)
    (hK : ∀ i, (∑ x ∈ X, f i x ^ Fintype.card ι) ≤ K) :
    (∑ x ∈ X, ∏ i, f i x) ≤ K := by
  classical
  have hB : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ x ∈ X, (∑ i, f i x ^ Fintype.card ι) / (Fintype.card ι : ℝ) :=
      sum_le_sum (fun x hx ↦ product_le_average_power (fun i ↦ f i x) (fun i ↦ hf i x hx))
    _ = (∑ i, ∑ x ∈ X, f i x ^ Fintype.card ι) / (Fintype.card ι : ℝ) := by rw [← sum_div, sum_comm]
    _ ≤ (∑ _i : ι, K) / (Fintype.card ι : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum fun i _ ↦ hK i) hB.le
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; field_simp

end PaperP1.FiniteProductPowerMean
