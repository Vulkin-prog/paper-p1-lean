module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # A local point evaluation bound from actual function and derivative square integrals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalSquareSampling
open MeasureTheory Set
open scoped RealInnerProductSpace

theorem local_square_bound (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ x, HasDerivAt f (g x) x) (a : ℝ) :
    ‖f a‖^2 ≤ 2*(∫ x in a..a+1, ‖f x‖^2) + (∫ x in a..a+1, ‖g x‖^2) := by
  let q : ℝ → ℝ := fun x ↦ ‖f x‖^2
  let r : ℝ → ℝ := fun x ↦ 2 * inner ℝ (f x) (g x)
  let E : ℝ → ℝ := fun x ↦ ‖f x‖^2 + ‖g x‖^2
  have hq : Continuous q := by dsimp only [q]; fun_prop
  have hr : Continuous r := by dsimp only [r]; fun_prop
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hEpos (x : ℝ) : 0 ≤ E x := by dsimp only [E]; positivity
  have hneg (x : ℝ) : -r x ≤ E x := by
    have hinner := norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)
    rw [Real.norm_eq_abs] at hinner
    have hlo := neg_abs_le (inner ℝ (f x) (g x))
    dsimp only [r,E]
    nlinarith [sq_nonneg (‖f x‖-‖g x‖)]
  have hpoint (s : ℝ) (hs : s ∈ Icc a (a+1)) : q a ≤ q s + ∫ x in a..a+1, E x := by
    have hFTC : (∫ x in a..s, r x) = q s - q a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ (hd x).norm_sq)
        (hr.intervalIntegrable a s)
    have hnegint : (∫ x in a..s, -r x) ≤ ∫ x in a..s, E x :=
      intervalIntegral.integral_mono_on hs.1 (hr.neg.intervalIntegrable a s)
        (hE.intervalIntegrable a s) (fun x hx ↦ hneg x)
    have hsubint : (∫ x in a..s, E x) ≤ ∫ x in a..a+1, E x :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall hEpos) (hE.intervalIntegrable a (a+1))
    rw [intervalIntegral.integral_neg, hFTC] at hnegint
    linarith
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a+1)
    (continuous_const.intervalIntegrable a (a+1))
    ((hq.add continuous_const).intervalIntegrable a (a+1)) hpoint
  change (∫ x in a..a+1, q a) ≤ ∫ x in a..a+1, q x + (∫ y in a..a+1, E y) at hint
  rw [intervalIntegral.integral_add (hq.intervalIntegrable a (a+1))
    (continuous_const.intervalIntegrable a (a+1))] at hint
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul] at hint
  have heq : (∫ x in a..a+1, E x) =
      (∫ x in a..a+1, ‖f x‖^2) + (∫ x in a..a+1, ‖g x‖^2) :=
    intervalIntegral.integral_add ((hf.norm.pow 2).intervalIntegrable a (a+1))
      ((hg.norm.pow 2).intervalIntegrable a (a+1))
  dsimp only [q] at hint
  rw [heq] at hint
  linarith
end LocalSquareSampling
