module

public import PaperP1.Arithmetic.WeightedKernelTail

/-! # Weighted large-kernel tails with several possible receiving windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedReceiverKernelTail

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.SmallPrimeBudget
open PaperP1.KernelSupportFibres PaperP1.WeightedKernelTail PaperP1.SupportRankinTail
open PaperP1.SmallKernelCount

def supportTail (m B : ℕ) (T : ℝ) (R : Finset ℕ) : ℝ :=
  (m : ℝ) ^ R.card * PaperP1.WeightedKernelTail.supportTail B T R

def weightedTail (m B X : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, supportTail m B T (roughSupport B n)

theorem supportTail_nonneg (m B : ℕ) (T : ℝ) (R : Finset ℕ) :
    0 ≤ supportTail m B T R :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg m) _) (PaperP1.WeightedKernelTail.supportTail_nonneg B T R)

theorem fibre_bound (m : ℕ) {B X : ℕ} (T : ℝ) {S R : Finset ℕ}
    (hS : S ⊆ smallPrimesUpTo B) (hR : R ⊆ roughPrimes B X) :
    (Nat.sqrt (X / (S.prod id * R.prod id)) : ℝ) * supportTail m B T R ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
        (if T < ((R.prod id : ℕ) : ℝ) then weight ((m * B : ℕ) : ℝ) (3 / 2) R else 0) := by
  calc
    _ = (m : ℝ) ^ R.card *
        ((Nat.sqrt (X / (S.prod id * R.prod id)) : ℝ) * PaperP1.WeightedKernelTail.supportTail B T R) := by
      unfold supportTail
      ring
    _ ≤ (m : ℝ) ^ R.card *
        ((X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
          (if T < ((R.prod id : ℕ) : ℝ) then weight B (3 / 2) R else 0)) :=
      mul_le_mul_of_nonneg_left (PaperP1.WeightedKernelTail.fibre_bound T hS hR) (by positivity)
    _ = _ := by
      by_cases hT : T < ((R.prod id : ℕ) : ℝ)
      · simp only [ite_eq_left hT, weight, Nat.cast_mul, mul_pow]
        ring
      · simp only [ite_eq_right hT, mul_zero]

theorem weighted_tail_euler (m B X : ℕ) (T τ : ℝ) (hT : 0 < T) (hτhalf : τ ≤ 1 / 2) :
    weightedTail m B X T ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2) * T ^ (-1 / 2 + τ) *
        ∏ p ∈ roughPrimes B X, (1 + ((m * B : ℕ) : ℝ) * (p : ℝ) ^ (-(1 + τ))) := by
  have htail := support_tail_le (roughPrimes B X) ((m * B : ℕ) : ℝ) (3 / 2) (1 / 2 - τ) T
    (fun p hp ↦ (mem_roughPrimes.mp hp).1.pos) (Nat.cast_nonneg _) (by linarith) hT
  have htail' : (∑ R ∈ (roughPrimes B X).powerset,
      if T < ((R.prod id : ℕ) : ℝ) then weight ((m * B : ℕ) : ℝ) (3 / 2) R else 0) ≤
      T ^ (-1 / 2 + τ) * ∏ p ∈ roughPrimes B X, (1 + ((m * B : ℕ) : ℝ) * (p : ℝ) ^ (-(1 + τ))) := by
    simpa only [show -(1 / 2 - τ) = (-1 / 2 + τ : ℝ) by ring,
      show 3 / 2 - (1 / 2 - τ) = (1 + τ : ℝ) by ring] using htail
  calc
    _ ≤ ∑ S ∈ (smallPrimesUpTo B).powerset, ∑ R ∈ (roughPrimes B X).powerset,
        (Nat.sqrt (X / (S.prod id * R.prod id)) : ℝ) * supportTail m B T R :=
      weighted_fibres B X (fun _ R ↦ supportTail m B T R) (fun _ R ↦ supportTail_nonneg m B T R)
    _ ≤ ∑ S ∈ (smallPrimesUpTo B).powerset, ∑ R ∈ (roughPrimes B X).powerset,
        (X : ℝ) ^ (1 / 2 : ℝ) * (∏ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ))) *
          (if T < ((R.prod id : ℕ) : ℝ) then weight ((m * B : ℕ) : ℝ) (3 / 2) R else 0) :=
      sum_le_sum (fun S hS ↦ sum_le_sum (fun R hR ↦ fibre_bound m T
        (mem_powerset.mp hS) (mem_powerset.mp hR)))
    _ = ((X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2)) *
        (∑ R ∈ (roughPrimes B X).powerset,
          if T < ((R.prod id : ℕ) : ℝ) then weight ((m * B : ℕ) : ℝ) (3 / 2) R else 0) := by
      unfold eulerProduct
      rw [prod_one_add]
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail'
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) (eulerProduct_nonneg B _))

theorem rough_euler_bound (m B X : ℕ) (τ : ℝ) (hB : 1 ≤ B) (hτ : 0 < τ) :
    (∏ p ∈ roughPrimes B X, (1 + ((m * B : ℕ) : ℝ) * (p : ℝ) ^ (-(1 + τ)))) ≤
      Real.exp (m * PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
  have htail := PaperP1.ClippedPowerSum.finite_tail_le_power (roughPrimes B X) (1 + τ) B
    (by linarith) (by exact_mod_cast hB) (fun p hp ↦ by exact_mod_cast (mem_roughPrimes.mp hp).2.2)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  calc
    _ ≤ Real.exp (∑ p ∈ roughPrimes B X, ((m * B : ℕ) : ℝ) * (p : ℝ) ^ (-(1 + τ))) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ by positivity)
    _ ≤ Real.exp (((m * B : ℕ) : ℝ) * (PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - (1 + τ)))) := by
      apply Real.exp_le_exp.mpr
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = _ := by
      congr 1
      rw [Nat.cast_mul, show (m : ℝ) * B * (PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - (1 + τ))) =
        m * PaperP1.PowerSeriesTail.constant (1 + τ) * ((B : ℝ) * (B : ℝ) ^ (1 - (1 + τ))) by ring]
      congr 1
      calc
        (B : ℝ) * (B : ℝ) ^ (1 - (1 + τ)) = (B : ℝ) ^ (1 : ℝ) * (B : ℝ) ^ (1 - (1 + τ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hBpos]; congr 1; ring

theorem weighted_tail_exp (m B X : ℕ) (T τ : ℝ) (hB : 1 ≤ B) (hT : 0 < T)
    (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    weightedTail m B X T ≤ Real.sqrt X * T ^ (-1 / 2 + τ) *
      Real.exp (2 * Real.sqrt B + m * PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
  have hsmall := eulerProduct_le_exp B (1 / 2) (by norm_num) (by norm_num)
  have hsmall' : eulerProduct B (1 / 2) ≤ Real.exp (2 * Real.sqrt B) := by
    convert hsmall using 1; norm_num [← Real.sqrt_eq_rpow, div_eq_mul_inv]; ring
  have hlarge := rough_euler_bound m B X τ hB hτ
  calc
    _ ≤ (X : ℝ) ^ (1 / 2 : ℝ) * eulerProduct B (1 / 2) * T ^ (-1 / 2 + τ) *
        ∏ p ∈ roughPrimes B X, (1 + ((m * B : ℕ) : ℝ) * (p : ℝ) ^ (-(1 + τ))) :=
      weighted_tail_euler m B X T τ hT hτhalf
    _ ≤ (X : ℝ) ^ (1 / 2 : ℝ) * Real.exp (2 * Real.sqrt B) * T ^ (-1 / 2 + τ) *
        Real.exp (m * PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall' (by positivity)) (by positivity)
      · exact hlarge
      · exact prod_nonneg (fun p _ ↦ by positivity)
      · positivity
    _ = _ := by simp only [Real.exp_add, Real.sqrt_eq_rpow]; ring

end PaperP1.WeightedReceiverKernelTail
