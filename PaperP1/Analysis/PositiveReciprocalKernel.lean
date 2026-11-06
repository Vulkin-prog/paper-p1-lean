module

public import PaperP1.Analysis.LogarithmicShiftPhase
public import PaperP1.Analysis.ReciprocalDifferenceBounds
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PositiveReciprocalKernel
open MeasureTheory PaperP1 ReciprocalFiniteDifferences

theorem coefficient_pos (m : ℕ) (hm : 0 < m) (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) :
    0 < coefficient m hs := by
  induction hs generalizing m with
  | nil => simp [coefficient]
  | cons h hs ih =>
    have hh0 : 0 < h := hhs h List.mem_cons_self
    have hTail : ∀ v ∈ hs, 0 < v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    exact mul_pos (mul_pos hh0 hmR) (ih (m+1) (by omega) hTail)

theorem kernel_nonneg (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ kernel hs m x := by
  have hSum := ReciprocalDifferenceBounds.shifts_sum_nonneg hs hhs
  have hCoeff := coefficient_nonneg m hs hhs
  have hBound := (ReciprocalDifferenceBounds.kernel_bounds hs hhs m x hx).1
  exact (div_nonneg hCoeff (by positivity)).trans hBound

theorem kernel_pos (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 < x) :
    0 < kernel hs m x := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hSum := ReciprocalDifferenceBounds.shifts_sum_nonneg hs hNN
  have hCoeff := coefficient_pos m hm hs hhs
  have hBound := (ReciprocalDifferenceBounds.kernel_bounds hs hNN m x hx).1
  exact (div_pos hCoeff (by positivity)).trans_le hBound

theorem first_coefficient (hs : List ℝ) : coefficient 1 hs=(hs.length.factorial : ℝ)*hs.prod := by
  rw [coefficient_identity,Nat.one_ascFactorial]

theorem inverse_first_hasDerivAt (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y ↦ 1/kernel hs 1 y) (kernel hs 2 x/(kernel hs 1 x)^2) x := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hPos := kernel_pos hs hhs 1 (by norm_num) x hx
  have hh := (hasDerivAt_kernel hs hNN 1 x hx).inv hPos.ne'
  convert hh using 1
  · funext y
    simp only [one_div,Pi.inv_apply]
  · simp only [Nat.cast_one,neg_mul,one_mul,neg_neg]

theorem inverse_derivative_nonneg (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (x : ℝ) (hx : 0 < x) :
    0 ≤ kernel hs 2 x/(kernel hs 1 x)^2 := div_nonneg (kernel_nonneg hs hhs 2 x hx) (sq_nonneg _)

theorem inverse_integral (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ y in A..B, kernel hs 2 y/(kernel hs 1 y)^2)=1/kernel hs 1 B-1/kernel hs 1 A := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hSubset : Set.Icc A B ⊆ Set.Ioi 0 := fun _y hy ↦ hA.trans_le hy.1
  have hC : ContinuousOn (fun y ↦ kernel hs 2 y/(kernel hs 1 y)^2) (Set.Icc A B) :=
    ((continuousOn_kernel hs hNN 2).mono hSubset).div (((continuousOn_kernel hs hNN 1).mono hSubset).pow 2)
      (fun y hy ↦ pow_ne_zero 2 (kernel_pos hs hhs 1 (by norm_num) y (hA.trans_le hy.1)).ne')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y ↦ 1/kernel hs 1 y)
  · intro y hy
    rw [Set.uIcc_of_le hAB] at hy
    exact inverse_first_hasDerivAt hs hhs y (hA.trans_le hy.1)
  · exact hC.intervalIntegrable_of_Icc hAB
end PaperP1.PositiveReciprocalKernel
