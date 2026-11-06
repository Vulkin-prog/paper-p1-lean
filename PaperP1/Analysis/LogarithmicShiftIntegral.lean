module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import PaperP1.Analysis.LogarithmicShiftPhase

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicShiftIntegral
open Finset MeasureTheory PaperP1 LogarithmicShiftPhase
open scoped Classical

theorem continuousOn_function (t h A B : ℝ) (hA : 0 < A) (hh : 0 ≤ h) :
    ContinuousOn (function t h) (Set.Icc A B) := by
  intro x hx
  have hxpos : 0 < x := hA.trans_le hx.1
  exact (hasDerivAt_function t h x hxpos (by linarith)).continuousAt.continuousWithinAt

theorem continuous_amplitude (t h : ℝ) : Continuous (amplitude t h) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_amplitude t h x).continuousAt)

theorem continuous_amplitudeDeriv (t h : ℝ) : Continuous (amplitudeDeriv t h) := by
  unfold amplitudeDeriv
  fun_prop

theorem product_hasDeriv (t h x : ℝ) (ht : t ≠ 0) (hh : 0 < h) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ function t h y*amplitude t h y)
      (function t h x+function t h x*amplitudeDeriv t h x) x := by
  have hp := (hasDerivAt_function t h x hx (by linarith)).mul (hasDerivAt_amplitude t h x)
  convert hp using 1
  rw [derivative_amplitude_cancel t h x ht hh hx]

theorem integral_identity (t h A B : ℝ) (ht : t ≠ 0) (hh : 0 < h) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, function t h x)=function t h B*amplitude t h B-function t h A*amplitude t h A-
      (∫ x in A..B, function t h x*amplitudeDeriv t h x) := by
  have hcont := continuousOn_function t h A B hA hh.le
  have hu : IntervalIntegrable (function t h) volume A B := hcont.intervalIntegrable_of_Icc hAB
  have hr : IntervalIntegrable (fun x ↦ function t h x*amplitudeDeriv t h x) volume A B :=
    (hcont.mul (continuous_amplitudeDeriv t h).continuousOn).intervalIntegrable_of_Icc hAB
  have hf : (∫ x in A..B, function t h x+function t h x*amplitudeDeriv t h x)=
      function t h B*amplitude t h B-function t h A*amplitude t h A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hAB] at hx
      exact product_hasDeriv t h x ht hh (hA.trans_le hx.1)
    · exact hu.add hr
  rw [intervalIntegral.integral_add hu hr] at hf
  exact eq_sub_iff_add_eq.mpr hf

theorem integral_norm_bound (t h A B : ℝ) (ht : t ≠ 0) (hh : 0 < h) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ x in A..B, function t h x‖ ≤ 4*B*(B+h)/(|t| * h) := by
  have hB : 0 < B := hA.trans_le hAB
  let D := |t| * h
  have hD : 0 < D := mul_pos (abs_pos.mpr ht) hh
  let K := B*(B+h)/D
  have hbA : ‖function t h A*amplitude t h A‖ ≤ K := by
    rw [norm_mul,function_norm,one_mul,amplitude_norm t h A hA hh.le]
    apply div_le_div_of_nonneg_right ?_ hD.le
    exact mul_le_mul hAB (add_le_add hAB le_rfl) (by linarith) hB.le
  have hbB : ‖function t h B*amplitude t h B‖=K := by
    rw [norm_mul,function_norm,one_mul,amplitude_norm t h B hB hh.le]
  have hrem : ‖∫ x in A..B, function t h x*amplitudeDeriv t h x‖ ≤ 2*K := by
    have hc := intervalIntegral.norm_integral_le_of_norm_le_const (a := A) (b := B)
      (C := (2*B+h)/D) (f := fun x : ℝ ↦ function t h x*amplitudeDeriv t h x) (fun x hx ↦ by
        have hx' : x ∈ Set.Ioc A B := by simpa only [Set.uIoc_of_le hAB] using hx
        have hxp : 0 < x := hA.trans_le hx'.1.le
        rw [norm_mul,function_norm,one_mul,amplitudeDeriv_norm t h x hxp hh.le]
        exact div_le_div_of_nonneg_right (by linarith [hx'.2] : 2*x+h ≤ 2*B+h) hD.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hAB)] at hc
    have hp : (2*B+h)*(B-A) ≤ 2*B*(B+h) := by
      have h1 := mul_nonneg hA.le (show 0 ≤ 2*B+h by linarith)
      have h2 := mul_nonneg hB.le hh.le
      nlinarith
    calc
      _ ≤ ((2*B+h)/D)*(B-A) := hc
      _ = ((2*B+h)*(B-A))/D := by ring
      _ ≤ (2*B*(B+h))/D := div_le_div_of_nonneg_right hp hD.le
      _ = 2*K := by dsimp only [K]; ring
  rw [integral_identity t h A B ht hh hA hAB]
  calc
    _ ≤ ‖function t h B*amplitude t h B-function t h A*amplitude t h A‖+
        ‖∫ x in A..B, function t h x*amplitudeDeriv t h x‖ := norm_sub_le _ _
    _ ≤ (K+K)+2*K := add_le_add ((norm_sub_le _ _).trans (add_le_add hbB.le hbA)) hrem
    _ = _ := by dsimp only [K,D]; ring
end PaperP1.LogarithmicShiftIntegral
