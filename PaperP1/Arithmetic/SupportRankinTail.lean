module

public import PaperP1.Arithmetic.FiniteEulerRankin
public import PaperP1.Analysis.ClippedPowerSum

/-! # Rankin's inequality for the upper tail of finite support products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SupportRankinTail

open Finset PaperP1.RankinComparison

def weight (a s : ℝ) (R : Finset ℕ) : ℝ :=
  a ^ R.card * ((R.prod id : ℕ) : ℝ) ^ (-s)

theorem weight_product (a s : ℝ) (R : Finset ℕ) :
    weight a s R = ∏ p ∈ R, (a * (p : ℝ) ^ (-s)) := by
  rw [weight, prod_mul_distrib, prod_const, cast_prod_rpow]

theorem weight_nonneg (a s : ℝ) (ha : 0 ≤ a) (R : Finset ℕ) :
    0 ≤ weight a s R := mul_nonneg (pow_nonneg ha _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem rankin_term (a s δ T : ℝ) (R : Finset ℕ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hT : 0 < T) (hR : ∀ p ∈ R, 1 ≤ p)
    (hTR : T ≤ ((R.prod id : ℕ) : ℝ)) :
    weight a s R ≤ T ^ (-δ) * weight a (s - δ) R := by
  have hprod : (0 : ℝ) < R.prod id := by
    exact_mod_cast prod_pos (fun p hp ↦ zero_lt_one.trans_le (hR p hp))
  have hpow := Real.rpow_le_rpow_of_nonpos hT hTR (by linarith : -δ ≤ 0)
  calc
    _ = ((R.prod id : ℕ) : ℝ) ^ (-δ) * weight a (s - δ) R := by
      unfold weight
      rw [show ((R.prod id : ℕ) : ℝ) ^ (-δ) *
          (a ^ R.card * ((R.prod id : ℕ) : ℝ) ^ (-(s - δ))) =
          a ^ R.card * (((R.prod id : ℕ) : ℝ) ^ (-δ) *
            ((R.prod id : ℕ) : ℝ) ^ (-(s - δ))) by ring,
        ← Real.rpow_add hprod]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (weight_nonneg a (s - δ) ha R)

theorem support_tail_le (P : Finset ℕ) (a s δ T : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hT : 0 < T) :
    (∑ R ∈ P.powerset, if T < ((R.prod id : ℕ) : ℝ) then weight a s R else 0) ≤
      T ^ (-δ) * ∏ p ∈ P, (1 + a * (p : ℝ) ^ (-(s - δ))) := by
  calc
    _ ≤ ∑ R ∈ P.powerset, T ^ (-δ) * weight a (s - δ) R := by
      apply sum_le_sum
      intro R hR
      split_ifs with hTR
      · exact rankin_term a s δ T R ha hδ hT (fun p hp ↦ hP p (mem_powerset.mp hR hp)) hTR.le
      · exact mul_nonneg (Real.rpow_nonneg hT.le _) (weight_nonneg a (s - δ) ha R)
    _ = _ := by
      rw [← mul_sum]
      simp_rw [weight_product]
      rw [← prod_one_add]

theorem rough_euler_bound (P : Finset ℕ) (B τ : ℝ)
    (hB : 1 ≤ B) (hτ : 0 < τ) (hP : ∀ p ∈ P, B < (p : ℝ)) :
    (∏ p ∈ P, (1 + B * (p : ℝ) ^ (-(1 + τ)))) ≤
      Real.exp (PaperP1.PowerSeriesTail.constant (1 + τ) * B ^ (1 - τ)) := by
  have htail := PaperP1.ClippedPowerSum.finite_tail_le_power P (1 + τ) B
    (by linarith) hB hP
  have hBpos : 0 < B := by linarith
  calc
    _ ≤ Real.exp (∑ p ∈ P, B * (p : ℝ) ^ (-(1 + τ))) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ mul_nonneg hBpos.le
        (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    _ ≤ Real.exp (B * (PaperP1.PowerSeriesTail.constant (1 + τ) * B ^ (1 - (1 + τ)))) := by
      apply Real.exp_le_exp.mpr
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left htail hBpos.le
    _ = _ := by
      congr 1
      rw [mul_left_comm]
      congr 1
      calc
        B * B ^ (1 - (1 + τ)) = B ^ (1 : ℝ) * B ^ (1 - (1 + τ)) := by rw [Real.rpow_one]
        _ = B ^ (1 - τ) := by rw [← Real.rpow_add hBpos]; congr 1; ring

end PaperP1.SupportRankinTail
