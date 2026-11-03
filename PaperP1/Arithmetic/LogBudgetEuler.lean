module

public import PaperP1.Arithmetic.WeightedPrimeSum
public import PaperP1.Arithmetic.PrimeSetEuler

/-! # A finite logarithmic-budget Euler bound split at an arbitrary prime threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogBudgetEuler

open Finset PaperP1.DefectCounting PaperP1.SmoothSquarefreeCount PaperP1.WeightedPrimeSum

theorem euler_one_le (P : Finset ℕ) : 1 ≤ eulerProduct P (1 / 2) := by
  apply one_le_prod₀
  intro p _
  have h : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  linarith only [h]

theorem euler_union (P Q : Finset ℕ) :
    eulerProduct (P ∪ Q) (1 / 2) ≤ eulerProduct P (1 / 2) * eulerProduct Q (1 / 2) := by
  have h := mul_le_mul_of_nonneg_left (euler_one_le (P ∩ Q)) (eulerProduct_nonneg (P ∪ Q) (1 / 2))
  rw [mul_one] at h
  exact h.trans_eq (prod_union_inter (s₁ := P) (s₂ := Q) (f := fun p : ℕ ↦ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ))))

theorem finite_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (Y : ℕ) (hY : 2 ≤ Y)
    (K : ℝ) (hK : (∑ p ∈ P, Real.log p) ≤ K) :
    eulerProduct P (1 / 2) ≤ Real.exp (smallPrimeConstant * Real.sqrt Y / Real.log Y +
      K / (Real.sqrt Y * Real.log Y)) := by
  classical
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hy1 : (1 : ℝ) < Y := by exact_mod_cast hY
  have hl : 0 < Real.log Y := Real.log_pos hy1
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hy
  let low := P.filter fun p ↦ p ≤ Y
  let high := P.filter fun p ↦ ¬ p ≤ Y
  have hlow : low ⊆ smallPrimesUpTo Y := by
    intro p hp
    obtain ⟨hp, hcut⟩ := mem_filter.mp hp
    exact mem_smallPrimesUpTo.mpr ⟨hP p hp, hcut⟩
  have hsmall : (∑ p ∈ low, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ smallPrimeConstant * Real.sqrt Y / Real.log Y := by
    have hprime := primeSum_mul_log_le_uniform (Y : ℝ) (1 / 2) hy (by norm_num) (by norm_num)
    rw [Nat.floor_natCast, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow] at hprime
    exact (sum_le_sum_of_subset_of_nonneg hlow (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)).trans
      ((le_div_iff₀ hl).mpr hprime)
  have hterm (p : ℕ) (hp : p ∈ high) :
      (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.log p / (Real.sqrt Y * Real.log Y) := by
    have hyp : (Y : ℝ) ≤ p := by exact_mod_cast (le_of_not_ge (mem_filter.mp hp).2)
    calc
      _ ≤ (Real.sqrt Y)⁻¹ := by
        rw [← PaperP1.rpow_neg_one_half_eq_inv_sqrt _ hy.le]
        exact Real.rpow_le_rpow_of_nonpos hy hyp (by norm_num)
      _ = Real.log Y / (Real.sqrt Y * Real.log Y) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (Real.log_le_log hy hyp) (mul_nonneg hs.le hl.le)
  have hhigh : (∑ p ∈ high, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ K / (Real.sqrt Y * Real.log Y) := by
    calc
      _ ≤ ∑ p ∈ high, Real.log p / (Real.sqrt Y * Real.log Y) := sum_le_sum hterm
      _ = (∑ p ∈ high, Real.log p) / (Real.sqrt Y * Real.log Y) := (sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right
        ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ ↦ Real.log_natCast_nonneg p)).trans hK)
        (mul_nonneg hs.le hl.le)
  have hsplit := sum_filter_add_sum_filter_not P (fun p ↦ p ≤ Y) (fun p : ℕ ↦ (p : ℝ) ^ (-(1 / 2 : ℝ)))
  have hsum : (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      smallPrimeConstant * Real.sqrt Y / Real.log Y + K / (Real.sqrt Y * Real.log Y) := by
    change (∑ p ∈ low, _) + (∑ p ∈ high, _) = _ at hsplit
    linarith only [hsplit, hsmall, hhigh]
  exact (Real.prod_one_add_le_exp_sum P (fun p : ℕ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 / 2 : ℝ)))).trans
    (Real.exp_le_exp.mpr hsum)

end PaperP1.LogBudgetEuler
