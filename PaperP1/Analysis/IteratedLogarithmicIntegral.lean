module

public import PaperP1.Analysis.LogarithmicShiftIntegral
public import PaperP1.Analysis.IteratedLogarithmicPhase
public import PaperP1.Analysis.IteratedOscillationAmplitude
public import PaperP1.Analysis.PositiveReciprocalKernel
public import PaperP1.Analysis.ReciprocalDifferenceBounds
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IteratedLogarithmicIntegral
open MeasureTheory PaperP1 ReciprocalFiniteDifferences IteratedLogarithmicPhase IteratedOscillationAmplitude

theorem continuousOn_function (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t A B : ℝ) (hA : 0 < A) :
    ContinuousOn (function hs t) (Set.Icc A B) := by
  intro x hx
  exact (hasDerivAt_function hs hhs t x (hA.trans_le hx.1)).continuousAt.continuousWithinAt

theorem continuousOn_inverse_derivative (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (A B : ℝ) (hA : 0 < A) :
    ContinuousOn (fun y ↦ kernel hs 2 y/(kernel hs 1 y)^2) (Set.Icc A B) := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hSubset : Set.Icc A B ⊆ Set.Ioi 0 := fun _y hy ↦ hA.trans_le hy.1
  exact ((continuousOn_kernel hs hNN 2).mono hSubset).div (((continuousOn_kernel hs hNN 1).mono hSubset).pow 2)
    (fun y hy ↦ pow_ne_zero 2 (PositiveReciprocalKernel.kernel_pos hs hhs 1 (by norm_num) y (hA.trans_le hy.1)).ne')

theorem continuousOn_amplitudeDeriv (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t A B : ℝ) (hA : 0 < A) :
    ContinuousOn (amplitudeDeriv hs t) (Set.Icc A B) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_inverse_derivative hs hhs A B hA)).div_const (denominator t)

theorem integral_identity (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t A B : ℝ)
    (ht : t ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, function hs t x)=function hs t B*amplitude hs t B-function hs t A*amplitude hs t A-
      (∫ x in A..B, function hs t x*amplitudeDeriv hs t x) := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hCont := continuousOn_function hs hNN t A B hA
  have hu : IntervalIntegrable (function hs t) volume A B := hCont.intervalIntegrable_of_Icc hAB
  have hr : IntervalIntegrable (fun x ↦ function hs t x*amplitudeDeriv hs t x) volume A B :=
    (hCont.mul (continuousOn_amplitudeDeriv hs hhs t A B hA)).intervalIntegrable_of_Icc hAB
  have hf : (∫ x in A..B, function hs t x+function hs t x*amplitudeDeriv hs t x)=
      function hs t B*amplitude hs t B-function hs t A*amplitude hs t A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hAB] at hx
      exact product_hasDeriv hs hhs t x ht (hA.trans_le hx.1)
    · exact hu.add hr
  rw [intervalIntegral.integral_add hu hr] at hf
  exact eq_sub_iff_add_eq.mpr hf

theorem integral_norm_bound (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t A B : ℝ)
    (ht : t ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ x in A..B, function hs t x‖ ≤ 2/(|t| * kernel hs 1 B) := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hB : 0 < B := hA.trans_le hAB
  have hG : IntervalIntegrable (fun x ↦ (kernel hs 2 x/(kernel hs 1 x)^2)/|t|) volume A B :=
    ((continuousOn_inverse_derivative hs hhs A B hA).div_const |t|).intervalIntegrable_of_Icc hAB
  have hRem := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hAB
    (f := fun x ↦ function hs t x*amplitudeDeriv hs t x)
    (g := fun x ↦ (kernel hs 2 x/(kernel hs 1 x)^2)/|t|)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      have hxp : 0 < x := hA.trans_le hx.1.le
      rw [norm_mul,function_norm,one_mul,amplitudeDeriv_norm hs hNN t x hxp])) hG
  rw [intervalIntegral.integral_div,PositiveReciprocalKernel.inverse_integral hs hhs A B hA hAB,sub_div] at hRem
  have hEA : ‖function hs t A*amplitude hs t A‖=(1/kernel hs 1 A)/|t| := by
    rw [norm_mul,function_norm,one_mul,amplitude_norm hs hhs t A hA]
  have hEB : ‖function hs t B*amplitude hs t B‖=(1/kernel hs 1 B)/|t| := by
    rw [norm_mul,function_norm,one_mul,amplitude_norm hs hhs t B hB]
  rw [integral_identity hs hhs t A B ht hA hAB]
  calc
    _ ≤ ‖function hs t B*amplitude hs t B-function hs t A*amplitude hs t A‖+
        ‖∫ x in A..B, function hs t x*amplitudeDeriv hs t x‖ := norm_sub_le _ _
    _ ≤ ((1/kernel hs 1 B)/|t|+(1/kernel hs 1 A)/|t|)+
        ((1/kernel hs 1 B)/|t|-(1/kernel hs 1 A)/|t|) :=
      add_le_add ((norm_sub_le _ _).trans (by rw [hEA,hEB])) hRem
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem explicit_integral_bound (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t A B : ℝ)
    (ht : t ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ x in A..B, function hs t x‖ ≤
      2*(B+hs.sum)^(hs.length+1)/(|t| * (hs.length.factorial : ℝ)*hs.prod) := by
  have hB : 0 < B := hA.trans_le hAB
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hSum := ReciprocalDifferenceBounds.shifts_sum_nonneg hs hNN
  have hCoeff := PositiveReciprocalKernel.coefficient_pos 1 (by norm_num) hs hhs
  have hLower := (ReciprocalDifferenceBounds.kernel_bounds hs hNN 1 B hB).1
  have hInv := one_div_le_one_div_of_le (div_pos hCoeff (by positivity)) hLower
  rw [one_div_div] at hInv
  have hMul := mul_le_mul_of_nonneg_left hInv (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg t))
  calc
    _ ≤ 2/(|t| * kernel hs 1 B) := integral_norm_bound hs hhs t A B ht hA hAB
    _ = (2/|t|)*(1/kernel hs 1 B) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ ≤ (2/|t|)*((B+hs.sum)^(1+hs.length)/coefficient 1 hs) := hMul
    _ = _ := by
      rw [PositiveReciprocalKernel.first_coefficient,Nat.add_comm 1 hs.length]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
end PaperP1.IteratedLogarithmicIntegral
