module

public import PaperP1.Analysis.AmplificationBudgetBound
public import PaperP1.Analysis.PrimeMomentExponentialBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SecondThresholdCardBudget
open Finset PaperP1
open scoped Classical

theorem threshold_identity (q : ℝ) (hq : 0 < q) (k : ℕ) :
    ((q^(-1/40 : ℝ))^(2*k))⁻¹=Real.exp ((k : ℝ)*Real.log q/20) := by
  have he : (q^(-1/40 : ℝ))^(2*k)=Real.exp (-((k : ℝ)*Real.log q/20)) := by
    rw [Real.rpow_def_of_pos hq,← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he,← Real.exp_neg,neg_neg]

theorem weighted_bound (x z C q : ℝ) (hx : 100000 ≤ x) (hz : x^5 ≤ z)
    (hlog : Real.log z=x) (hCe : C ≤ Real.exp x) (hq : 1 < q)
    (k H : ℕ) (hk : 1 ≤ k) (hH : 1 ≤ H) (hkz : (k : ℝ) ≤ z)
    (hkr : (k : ℝ) ≤ 3*z/x^2) (hkLog : (k : ℝ)*Real.log q ≤ z+x^3)
    (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    C*Real.exp (6*((k : ℝ)/(H : ℝ)))*(2+9*((k : ℝ)/(H : ℝ))^2)*
      AmplifiedPrimeProductMean.budget k P/(q^(-1/40 : ℝ))^(2*k) ≤ Real.exp (z/19) := by
  have hProd := PrimeMomentExponentialBudget.combined_bound x z C (by linarith only [hx])
    hz hlog hCe k H hk hH hkz hkr P hMass
  have hqPos : 0 < q := by linarith only [hq]
  have hThreshold := Real.exp_le_exp.mpr (show (k : ℝ)*Real.log q/20 ≤ (z+x^3)/20 by linarith only [hkLog])
  rw [div_eq_mul_inv,threshold_identity q hqPos k]
  calc
    _ ≤ Real.exp (40*z/x)*Real.exp ((z+x^3)/20) :=
      mul_le_mul hProd hThreshold (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (40*z/x+(z+x^3)/20) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (PrimeMomentExponentialBudget.final_exponent_bound x z hx hz)
end PaperP1.SecondThresholdCardBudget
