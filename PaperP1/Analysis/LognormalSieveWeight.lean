module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalSieveWeight
open PaperP1

def weight (A x : ℝ) : ℝ := Real.exp (-Real.log (x/A)-(Real.log (x/A))^2)

theorem weight_pos (A x : ℝ) : 0 < weight A x := Real.exp_pos _

theorem weight_upper (A x : ℝ) : weight A x ≤ Real.exp (1/4) := by
  apply Real.exp_le_exp.mpr
  nlinarith only [sq_nonneg (Real.log (x/A)+1/2)]

theorem gaussian_identity (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    weight A x=(A/x)*Real.exp (-(Real.log (x/A))^2) := by
  have hFirst : Real.exp (-Real.log (x/A))=A/x := by
    rw [Real.exp_neg,Real.exp_log (div_pos hx hA),inv_div]
  unfold weight
  rw [sub_eq_add_neg,Real.exp_add,hFirst]

theorem majorant_on_dyadic (A x : ℝ) (hA : 0 < A) (hLower : A ≤ x) (hUpper : x ≤ 2*A) :
    1 ≤ Real.exp 2*weight A x := by
  have hx : 0 < x := hA.trans_le hLower
  have hRatioLower : 1 ≤ x/A := (le_div_iff₀ hA).mpr (by simpa only [one_mul] using hLower)
  have hRatioUpper : x/A ≤ 2 := (div_le_iff₀ hA).mpr hUpper
  have hLog0 : 0 ≤ Real.log (x/A) := Real.log_nonneg hRatioLower
  have hLog1 : Real.log (x/A) ≤ 1 := by
    have hh := Real.log_le_log (div_pos hx hA) hRatioUpper
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh,ht]
  have hExp : Real.exp (-2) ≤ weight A x := by
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg hLog0 (sub_nonneg.mpr hLog1)
    nlinarith only [hh,hLog1]
  have hh := mul_le_mul_of_nonneg_left hExp (Real.exp_pos 2).le
  have he : Real.exp 2*Real.exp (-2)=1 := by rw [← Real.exp_add]; norm_num
  rw [he] at hh
  exact hh

theorem polynomial_tail_bound (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    weight A x ≤ Real.exp 1*A^3/x^3 := by
  have hLog := Real.log_div hx.ne' hA.ne'
  have hExp : weight A x ≤ Real.exp (1-3*Real.log (x/A)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [sq_nonneg (Real.log (x/A)-1)]
  apply hExp.trans_eq
  rw [hLog,show 1-3*(Real.log x-Real.log A)=1+3*Real.log A-3*Real.log x by ring,
    Real.exp_sub,Real.exp_add]
  have hNum : Real.exp (3*Real.log A)=A^3 := by
    have hh := Real.exp_nat_mul (Real.log A) 3
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [Real.exp_log hA] using hh
  have hDen : Real.exp (3*Real.log x)=x^3 := by
    have hh := Real.exp_nat_mul (Real.log x) 3
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [Real.exp_log hx] using hh
  rw [hNum,hDen]

theorem hasDerivAt_weight (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    HasDerivAt (weight A) (weight A x*(-(1+2*Real.log (x/A))/x)) x := by
  have hLog : HasDerivAt (fun y : ℝ ↦ Real.log y-Real.log A) (1/x) x :=
    by simpa only [one_div] using (Real.hasDerivAt_log hx.ne').sub_const (Real.log A)
  have hh := (hLog.neg.sub (hLog.pow 2)).exp
  have he : ∀ᶠ y in nhds x, weight A y=Real.exp (-(Real.log y-Real.log A)-(Real.log y-Real.log A)^2) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [weight,Real.log_div hy.ne' hA.ne']
  have hValue : Real.exp (-(Real.log x-Real.log A)-(Real.log x-Real.log A)^2)=weight A x := by
    rw [weight,Real.log_div hx.ne' hA.ne']
  have hActual := hh.congr_of_eventuallyEq he
  dsimp only [Pi.sub_apply,Pi.neg_apply,Pi.pow_apply] at hActual
  convert hActual using 1
  rw [hValue,Real.log_div hx.ne' hA.ne']
  ring
end PaperP1.LognormalSieveWeight
