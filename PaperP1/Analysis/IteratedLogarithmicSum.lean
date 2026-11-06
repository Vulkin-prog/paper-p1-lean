module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.IteratedLogarithmicIntegral
public import PaperP1.Analysis.IteratedLogarithmicPhase
public import PaperP1.Analysis.PositiveReciprocalKernel
public import PaperP1.Analysis.ReciprocalDifferenceBounds
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IteratedLogarithmicSum
open Finset MeasureTheory PaperP1 ReciprocalFiniteDifferences IteratedLogarithmicPhase
open scoped Classical

theorem derivative_bound (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t A x : ℝ) (hA : 0 < A) (hx : A ≤ x) :
    ‖function hs t x*((-Complex.I*(t : ℂ))*(kernel hs 1 x : ℂ))‖ ≤
      |t| * coefficient 1 hs/A^(1+hs.length) := by
  have hxp : 0 < x := hA.trans_le hx
  have hUpper := (ReciprocalDifferenceBounds.kernel_bounds hs hhs 1 x hxp).2
  have hCoeff := coefficient_nonneg 1 hs hhs
  have hPower := pow_le_pow_left₀ hA.le hx (1+hs.length)
  have hK := hUpper.trans (div_le_div_of_nonneg_left hCoeff (pow_pos hA _) hPower)
  rw [derivative_norm hs hhs t x hxp]
  exact (mul_le_mul_of_nonneg_left hK (abs_nonneg t)).trans_eq (by ring)

theorem local_variation (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t A x : ℝ)
    (hA : 0 < A) (hx : x ∈ Set.Icc A (A+1)) :
    ‖function hs t x-function hs t A‖ ≤ |t| * coefficient 1 hs/A^(1+hs.length) := by
  have hder : ∀ y ∈ Set.Icc A (A+1), HasDerivWithinAt (function hs t)
      (function hs t y*((-Complex.I*(t : ℂ))*(kernel hs 1 y : ℂ))) (Set.Icc A (A+1)) y :=
    fun y hy ↦ (hasDerivAt_function hs hhs t y (hA.trans_le hy.1)).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico A (A+1),
      ‖function hs t y*((-Complex.I*(t : ℂ))*(kernel hs 1 y : ℂ))‖ ≤ |t| * coefficient 1 hs/A^(1+hs.length) :=
    fun y hy ↦ derivative_bound hs hhs t A y hA hy.1
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound x hx
  have hlen : x-A ≤ 1 := by linarith only [hx.2]
  have hCoeff := coefficient_nonneg 1 hs hhs
  have hScaled := mul_le_mul_of_nonneg_left hlen
    (show 0 ≤ |t| * coefficient 1 hs/A^(1+hs.length) by positivity)
  exact hh.trans (by simpa only [mul_one] using hScaled)

theorem unit_integral_error (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t A : ℝ) (hA : 0 < A) :
    ‖function hs t A-(∫ x in A..A+1, function hs t x)‖ ≤ |t| * coefficient 1 hs/A^(1+hs.length) := by
  have hc := IteratedLogarithmicIntegral.continuousOn_function hs hhs t A (A+1) hA
  have hi : IntervalIntegrable (function hs t) volume A (A+1) := hc.intervalIntegrable_of_Icc (by linarith)
  have he : function hs t A-(∫ x in A..A+1, function hs t x)=
      ∫ x in A..A+1, function hs t A-function hs t x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : A ≤ A+1)
    (f := fun x ↦ function hs t A-function hs t x) (g := fun _ ↦ |t| * coefficient 1 hs/A^(1+hs.length))
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_sub_rev]
      exact local_variation hs hhs t A x hA ⟨hx.1.le,hx.2⟩)) intervalIntegrable_const
  simpa using hh

theorem sum_integral_error (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (N M : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (t : ℝ) :
    ‖(∑ n ∈ Ico N M, function hs t n)-(∫ x in (N : ℝ)..(M : ℝ), function hs t x)‖ ≤
      ((M-N : ℕ) : ℝ)*(|t| * coefficient 1 hs/(N : ℝ)^(1+hs.length)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ k ∈ Set.Ico N M, IntervalIntegrable (function hs t) volume (k : ℝ) ((k+1 : ℕ) : ℝ) := by
    intro k hk
    have hkp : (0 : ℝ) < k := by exact_mod_cast hN.trans_le hk.1
    simpa only [Nat.cast_add,Nat.cast_one] using
      (IteratedLogarithmicIntegral.continuousOn_function hs hhs t k (k+1) hkp).intervalIntegrable_of_Icc (by linarith : (k : ℝ) ≤ k+1)
  have hAdjacent := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := function hs t)
    (a := fun n : ℕ ↦ (n : ℝ)) hNM hint
  have he : (∑ n ∈ Ico N M, function hs t n)-(∫ x in (N : ℝ)..(M : ℝ), function hs t x)=
      ∑ n ∈ Ico N M, (function hs t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function hs t x)) := by
    rw [sum_sub_distrib,hAdjacent]
  rw [he]
  have hCoeff := coefficient_nonneg 1 hs hhs
  calc
    _ ≤ ∑ n ∈ Ico N M, ‖function hs t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function hs t x)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ico N M, |t| * coefficient 1 hs/(N : ℝ)^(1+hs.length) := by
      apply sum_le_sum
      intro n hn
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have hnp : 0 < (n : ℝ) := hNR.trans_le hnN
      have hu := unit_integral_error hs hhs t n hnp
      rw [← Nat.cast_one,← Nat.cast_add] at hu
      exact hu.trans (div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg t) hCoeff)
        (pow_pos hNR _) (pow_le_pow_left₀ hNR.le hnN _))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ico]

theorem integer_sum_bound (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (N M : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N M, function hs t n‖ ≤
      2*((M : ℝ)+hs.sum)^(hs.length+1)/(|t| * (hs.length.factorial : ℝ)*hs.prod)+
      ((M-N : ℕ) : ℝ)*(|t| * ((hs.length.factorial : ℝ)*hs.prod)/(N : ℝ)^(hs.length+1)) := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hErr := sum_integral_error hs hNN N M hN hNM t
  rw [PositiveReciprocalKernel.first_coefficient,Nat.add_comm 1 hs.length] at hErr
  have hInt := IteratedLogarithmicIntegral.explicit_integral_bound hs hhs t N M ht hNR hNMR
  have hh : ‖∑ n ∈ Ico N M, function hs t n‖ ≤
      ‖(∑ n ∈ Ico N M, function hs t n)-(∫ x in (N : ℝ)..(M : ℝ), function hs t x)‖+
      ‖∫ x in (N : ℝ)..(M : ℝ), function hs t x‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      ((∑ n ∈ Ico N M, function hs t n)-(∫ x in (N : ℝ)..(M : ℝ), function hs t x))
      (∫ x in (N : ℝ)..(M : ℝ), function hs t x)
  exact hh.trans ((add_le_add hErr hInt).trans_eq (by ring))
end PaperP1.IteratedLogarithmicSum
