module

public import PaperP1.Arithmetic.KernelSupportFibres
public import PaperP1.Arithmetic.SupportRankinTail
public import PaperP1.Analysis.SmoothEulerProduct

/-! # A finite weighted upper tail for the actual large odd kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedKernelTail

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.DefectivePredicate
open PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.KernelSupportFibres
open PaperP1.RankinComparison PaperP1.SupportRankinTail PaperP1.SmallKernelCount

def supportTail (B : ℕ) (T : ℝ) (R : Finset ℕ) : ℝ :=
  if T < ((R.prod id : ℕ) : ℝ) then (B : ℝ) ^ R.card / (R.prod id : ℕ) else 0

def weightedTail (B X : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, supportTail B T (roughSupport B n)

theorem supportTail_nonneg (B : ℕ) (T : ℝ) (R : Finset ℕ) :
    0 ≤ supportTail B T R := by
  unfold supportTail
  split_ifs <;> positivity

theorem reciprocal_three_halves (r : ℝ) (hr : 0 < r) :
    r ^ (-(1 / 2 : ℝ)) / r = r ^ (-(3 / 2 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hr]
  congr 1
  ring

theorem fibre_bound {B X : ℕ} (T : ℝ) {S R : Finset ℕ}
    (hS : S ⊆ smallPrimesUpTo B) (hR : R ⊆ roughPrimes B X) :
    (Nat.sqrt (X / (S.prod id * R.prod id)) : ℝ) * supportTail B T R ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
        (if T < ((R.prod id : ℕ) : ℝ) then weight B (3 / 2) R else 0) := by
  have hSpos : 0 < S.prod id := prod_pos (fun p hp ↦ (mem_smallPrimesUpTo.mp (hS hp)).1.pos)
  have hRpos : 0 < R.prod id := prod_pos (fun p hp ↦ (mem_roughPrimes.mp (hR hp)).1.pos)
  have hd : 1 ≤ S.prod id * R.prod id := Nat.mul_pos hSpos hRpos
  have hroot := cast_sqrt_div_le_rankin (X := X) hd (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), cast_prod_rpow S] at hroot
  by_cases hT : T < ((R.prod id : ℕ) : ℝ)
  · rw [supportTail, ite_eq_left hT, ite_eq_left hT]
    calc
      _ ≤ ((X : ℝ) ^ (1 / 2 : ℝ) *
          ((∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) * ((R.prod id : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) *
            ((B : ℝ) ^ R.card / (R.prod id : ℕ)) :=
        mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = _ := by
        unfold weight
        rw [show (X : ℝ) ^ (1 / 2 : ℝ) *
            ((∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) * ((R.prod id : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
            ((B : ℝ) ^ R.card / (R.prod id : ℕ)) =
            ((X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ)))) *
              ((B : ℝ) ^ R.card * (((R.prod id : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) / (R.prod id : ℕ))) by ring,
          reciprocal_three_halves _ (by exact_mod_cast hRpos)]
  · simp only [supportTail, ite_eq_right hT, mul_zero]
    exact le_rfl

theorem weighted_tail_euler (B X : ℕ) (T τ : ℝ) (hT : 0 < T)
    (_hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    weightedTail B X T ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2) * T ^ (-1 / 2 + τ) *
        ∏ p ∈ roughPrimes B X, (1 + (B : ℝ) * (p : ℝ) ^ (-(1 + τ))) := by
  have htail := support_tail_le (roughPrimes B X) B (3 / 2) (1 / 2 - τ) T
    (fun p hp ↦ (mem_roughPrimes.mp hp).1.pos) (Nat.cast_nonneg B) (by linarith) hT
  have hsum : weightedTail B X T ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2) *
        (∑ R ∈ (roughPrimes B X).powerset,
          if T < ((R.prod id : ℕ) : ℝ) then weight B (3 / 2) R else 0) := by
    calc
      _ ≤ ∑ S ∈ (smallPrimesUpTo B).powerset, ∑ R ∈ (roughPrimes B X).powerset,
          (Nat.sqrt (X / (S.prod id * R.prod id)) : ℝ) * supportTail B T R :=
        weighted_fibres B X (fun _ R ↦ supportTail B T R) (fun _ R ↦ supportTail_nonneg B T R)
      _ ≤ ∑ S ∈ (smallPrimesUpTo B).powerset, ∑ R ∈ (roughPrimes B X).powerset,
          (X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
            (if T < ((R.prod id : ℕ) : ℝ) then weight B (3 / 2) R else 0) :=
        sum_le_sum (fun S hS ↦ sum_le_sum (fun R hR ↦ fibre_bound T
          (mem_powerset.mp hS) (mem_powerset.mp hR)))
      _ = _ := by
        unfold eulerProduct
        rw [prod_one_add]
        simp_rw [← mul_sum]
        rw [← sum_mul, ← mul_sum]
  have htail' : (∑ R ∈ (roughPrimes B X).powerset,
          if T < ((R.prod id : ℕ) : ℝ) then weight B (3 / 2) R else 0) ≤
      T ^ (-1 / 2 + τ) * ∏ p ∈ roughPrimes B X, (1 + (B : ℝ) * (p : ℝ) ^ (-(1 + τ))) := by
    simpa only [show -(1 / 2 - τ) = (-1 / 2 + τ : ℝ) by ring,
      show 3 / 2 - (1 / 2 - τ) = (1 + τ : ℝ) by ring] using htail
  exact hsum.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail'
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) (eulerProduct_nonneg B _)))

theorem weighted_tail_exp (B X : ℕ) (T τ : ℝ) (hB : 1 ≤ B) (hT : 0 < T)
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    weightedTail B X T ≤ Real.sqrt X * T ^ (-1 / 2 + τ) *
      Real.exp (2 * Real.sqrt B + PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
  have hsmall := eulerProduct_le_exp B (1 / 2) (by norm_num) (by norm_num)
  have hsmall' : eulerProduct B (1 / 2) ≤ Real.exp (2 * Real.sqrt B) := by
    convert hsmall using 1; norm_num [← Real.sqrt_eq_rpow, div_eq_mul_inv]; ring
  have hlarge := rough_euler_bound (roughPrimes B X) B τ (by exact_mod_cast hB) hτ
    (fun p hp ↦ by exact_mod_cast (mem_roughPrimes.mp hp).2.2)
  calc
    _ ≤ (X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2) * T ^ (-1 / 2 + τ) *
        ∏ p ∈ roughPrimes B X, (1 + (B : ℝ) * (p : ℝ) ^ (-(1 + τ))) :=
      weighted_tail_euler B X T τ hT hτ hτhalf
    _ ≤ (X : ℝ) ^ (1 / 2 : ℝ) * Real.exp (2 * Real.sqrt B) * T ^ (-1 / 2 + τ) *
        Real.exp (PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall' (by positivity)) (by positivity)
      · exact hlarge
      · exact prod_nonneg (fun p _ ↦ by positivity)
      · positivity
    _ = _ := by simp only [Real.exp_add, Real.sqrt_eq_rpow]; ring

end PaperP1.WeightedKernelTail
