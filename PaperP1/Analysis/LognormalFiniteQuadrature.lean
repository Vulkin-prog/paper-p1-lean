module

public import PaperP1.Analysis.ReciprocalSquareTail
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.LognormalWeightVariation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalFiniteQuadrature
open Finset Filter MeasureTheory PaperP1 LognormalPhaseVariation
open scoped Classical

theorem finite_sum_integral_error (A t : ℝ) (hA : 0 < A) (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖(∑ n ∈ Ico N M, function A t n)-(∫ x in (N : ℝ)..(M : ℝ), function A t x)‖ ≤
      2*(LognormalWeightVariation.constant+|t|)*A/(N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ k ∈ Set.Ico N M, IntervalIntegrable (function A t) volume (k : ℝ) ((k+1 : ℕ) : ℝ) := by
    intro k hk
    have hp : (0 : ℝ) < k := by exact_mod_cast hN.trans_le hk.1
    simpa only [Nat.cast_add,Nat.cast_one] using
      (continuousOn_function A t k (k+1) hA hp).intervalIntegrable_of_Icc (by linarith : (k : ℝ) ≤ k+1)
  have hCells := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
    (f := function A t) (a := fun n : ℕ ↦ (n : ℝ)) hNM hint
  have he : (∑ n ∈ Ico N M, function A t n)-(∫ x in (N : ℝ)..(M : ℝ), function A t x)=
      ∑ n ∈ Ico N M, (function A t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function A t x)) := by
    rw [sum_sub_distrib,hCells]
  rw [he]
  have hSquares := ReciprocalSquareTail.finite_bound (N : ℝ) hNR (Ico N M)
    (fun n hn ↦ by exact_mod_cast (mem_Ico.mp hn).1)
  have hC := LognormalWeightVariation.constant_pos
  calc
    _ ≤ ∑ n ∈ Ico N M, ‖function A t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function A t x)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ico N M, ((LognormalWeightVariation.constant+|t|)*A)*(1/(n : ℝ)^2) := by
      apply sum_le_sum
      intro n hn
      have hnp : (0 : ℝ) < n := by exact_mod_cast hN.trans_le (mem_Ico.mp hn).1
      have hh := unit_integral_error A t n hA hnp
      simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul] using hh
    _ = ((LognormalWeightVariation.constant+|t|)*A)*(∑ n ∈ Ico N M, 1/(n : ℝ)^2) := by rw [mul_sum]
    _ ≤ ((LognormalWeightVariation.constant+|t|)*A)*(2/(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hSquares (by positivity)
    _ = _ := by ring

theorem sqrt_cutoff_error (A t : ℝ) (hA : 0 < A) (M : ℕ) (hM : ⌈Real.sqrt A⌉₊ ≤ M) :
    ‖(∑ n ∈ Ico ⌈Real.sqrt A⌉₊ M, function A t n)-
      (∫ x in (⌈Real.sqrt A⌉₊ : ℝ)..(M : ℝ), function A t x)‖ ≤
      2*(LognormalWeightVariation.constant+|t|)*Real.sqrt A := by
  have hS : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hN : 0 < ⌈Real.sqrt A⌉₊ := Nat.ceil_pos.mpr hS
  have hNR : (0 : ℝ) < ⌈Real.sqrt A⌉₊ := by exact_mod_cast hN
  have hRatio : A/(⌈Real.sqrt A⌉₊ : ℝ) ≤ Real.sqrt A := by
    apply (div_le_iff₀ hNR).mpr
    have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (Real.sqrt A)) hS.le
    nlinarith only [hh,Real.sq_sqrt hA.le]
  have hBound := finite_sum_integral_error A t hA ⌈Real.sqrt A⌉₊ M hN hM
  have hC := LognormalWeightVariation.constant_pos
  have hScale := mul_le_mul_of_nonneg_left hRatio
    (by positivity : 0 ≤ 2*(LognormalWeightVariation.constant+|t|))
  exact hBound.trans (by simpa only [mul_div_assoc] using hScale)
end PaperP1.LognormalFiniteQuadrature
