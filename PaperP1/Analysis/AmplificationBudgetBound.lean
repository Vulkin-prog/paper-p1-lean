module

public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.PrimeProductDivisorCard

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.AmplificationBudgetBound
open Finset PaperP1
open scoped Classical

theorem budget_power_bound (k : ℕ) (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    AmplifiedPrimeProductMean.budget k P ≤ (32*(k : ℝ)^2)^k := by
  have h0 : (0 : ℝ) ≤ ∑ p ∈ P, 1/(p : ℝ) := sum_nonneg (fun p hp ↦ by positivity)
  have hm : (∑ p ∈ P, 1/(p : ℝ))^k ≤ 1 := pow_le_one₀ h0 hMass
  have hf : (k.factorial : ℝ) ≤ (k : ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  have hf2 := pow_le_pow_left₀ (Nat.cast_nonneg k.factorial : (0 : ℝ) ≤ k.factorial) hf 2
  have hk : ((k+1 : ℕ) : ℝ) ≤ (2 : ℝ)^k := by exact_mod_cast PrimeProductDivisorCard.successor_le_two_pow k
  unfold AmplifiedPrimeProductMean.budget
  calc
    _ ≤ ((k : ℝ)^k)^2*(16 : ℝ)^k*(2 : ℝ)^k*1 := by gcongr
    _ = ((k : ℝ)^2)^k*(16 : ℝ)^k*(2 : ℝ)^k := by
      rw [mul_one,← pow_mul,Nat.mul_comm k 2,pow_mul]
    _ = ((k : ℝ)^2*16*2)^k := by rw [mul_pow,mul_pow]
    _ = _ := by congr 1; ring

theorem threshold_budget_bound (x : ℝ) (hx : 2 ≤ x) (k : ℕ) (hk : (k : ℝ) ≤ x^3)
    (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    AmplifiedPrimeProductMean.budget k P/(1/x^10)^(2*k) ≤ x^(31*k) := by
  have hxp : 0 < x := by linarith
  have hk2 : (k : ℝ)^2 ≤ x^6 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hk 2
    nlinarith only [hh]
  have h32 : (32 : ℝ) ≤ x^5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 5
    norm_num at hh
    exact hh
  have hbase : 32*(k : ℝ)^2*x^20 ≤ x^31 := by
    have hm := mul_le_mul h32 hk2 (sq_nonneg (k : ℝ)) (pow_nonneg hxp.le 5)
    calc
      _ ≤ (x^5*x^6)*x^20 := mul_le_mul_of_nonneg_right hm (pow_nonneg hxp.le 20)
      _ = _ := by ring
  have he : ((32*(k : ℝ)^2)^k)/(1/x^10)^(2*k)=(32*(k : ℝ)^2*x^20)^k := by
    have hpow : (x^10)^(2*k)=(x^20)^k := by
      rw [← pow_mul,← pow_mul]
      congr 1
      ring
    rw [div_pow,one_pow,hpow,one_div,div_inv_eq_mul,← mul_pow]
  calc
    _ ≤ ((32*(k : ℝ)^2)^k)/(1/x^10)^(2*k) :=
      div_le_div_of_nonneg_right (budget_power_bound k P hMass) (by positivity)
    _ = (32*(k : ℝ)^2*x^20)^k := he
    _ ≤ (x^31)^k := pow_le_pow_left₀ (by positivity) hbase k
    _ = _ := by rw [← pow_mul]
end PaperP1.AmplificationBudgetBound
