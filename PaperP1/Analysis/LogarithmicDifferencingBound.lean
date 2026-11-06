module

public import PaperP1.Analysis.TriangularDifferencing
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PaperP1.Analysis.LogarithmicShiftSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicDifferencingBound
open Finset MeasureTheory PaperP1
open scoped Classical

def budget (N H : ℕ) (t : ℝ) : ℝ :=
  24*(N : ℝ)^2/|t|+|t| * (H : ℝ)^2/(N : ℝ)

theorem budget_nonneg (N H : ℕ) (t : ℝ) : 0 ≤ budget N H t := by unfold budget; positivity

theorem harmonic_bound (H : ℕ) : (∑ d ∈ Icc 1 H, 1/(d : ℝ)) ≤ 1+Real.log (H : ℝ) := by
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using harmonic_le_one_add_log H

theorem energy (N : ℕ) (t : ℝ) :
    (∑ n ∈ range N, ‖LogarithmicExponentialSum.function t (N+n)‖^2)=(N : ℝ) := by
  simp only [LogarithmicExponentialSum.function_norm,one_pow,sum_const,nsmul_eq_mul,card_range,mul_one]

theorem sum_reindex (N : ℕ) (t : ℝ) :
    (∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n)=
      ∑ n ∈ range N, LogarithmicExponentialSum.function t (N+n) := by
  rw [sum_Ico_eq_sum_range,show 2*N-N=N by omega]
  simp only [Nat.cast_add]

theorem inverse_correlation_bound (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) (t : ℝ) (ht : t ≠ 0)
    (d : ℕ) (hd : d ∈ Icc 1 H) :
    ‖ShiftedCorrelations.correlation N (fun n ↦ LogarithmicExponentialSum.function t (N+n)) d‖ ≤
      budget N H t/(d : ℝ) := by
  have hN : 0 < N := by omega
  have hdpos : 0 < d := by have h := (mem_Icc.mp hd).1; omega
  have hdH : d ≤ H := (mem_Icc.mp hd).2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := LogarithmicShiftSum.correlation_bound N d hN hdpos (hdH.trans hHN) t ht
  have hsq : (d : ℝ)^2 ≤ (H : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg d) (by exact_mod_cast hdH) 2
  have he : |t| * (d : ℝ)/(N : ℝ) ≤ (|t| * (H : ℝ)^2/(N : ℝ))/(d : ℝ) := by
    apply (le_div_iff₀ hdR).mpr
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (abs_nonneg t)) hNR.le
    convert hh using 1
    ring
  calc
    _ ≤ 24*(N : ℝ)^2/(|t| * (d : ℝ))+|t| * (d : ℝ)/(N : ℝ) := hs
    _ ≤ 24*(N : ℝ)^2/(|t| * (d : ℝ))+(|t| * (H : ℝ)^2/(N : ℝ))/(d : ℝ) := add_le_add le_rfl he
    _ = _ := by
      unfold budget
      field_simp [hNR.ne',hdR.ne',abs_ne_zero.mpr ht]

theorem parameter_bound (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ))*((N : ℝ)+2*budget N H t*(∑ d ∈ Icc 1 H, 1/(d : ℝ))) := by
  have hh := TriangularDifferencing.inverse_correlation_bound N H hH
    (fun n ↦ LogarithmicExponentialSum.function t (N+n)) (budget N H t) (budget_nonneg N H t)
    (inverse_correlation_bound N H hH hHN t ht)
  rw [energy] at hh
  rw [sum_reindex]
  exact hh

theorem logarithmic_bound (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ))*((N : ℝ)+2*budget N H t*(1+Real.log (H : ℝ))) := by
  exact (parameter_bound N H hH hHN t ht).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (harmonic_bound H) (mul_nonneg (by norm_num) (budget_nonneg N H t)))) (by positivity))

theorem expanded_bound (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖^2 ≤
      2*(N : ℝ)^2/(H : ℝ)+
      96*(N : ℝ)^3/((H : ℝ)*|t|)*(1+Real.log (N : ℝ))+
      4*|t| * (H : ℝ)*(1+Real.log (N : ℝ)) := by
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hHR : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hlog := Real.log_le_log hHr hHR
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_natCast_nonneg H
  have hfactor : ((N+H : ℕ) : ℝ)/(H : ℝ) ≤ 2*(N : ℝ)/(H : ℝ) := by
    apply div_le_div_of_nonneg_right ?_ hHr.le
    push_cast
    linarith
  calc
    _ ≤ (((N+H : ℕ) : ℝ)/(H : ℝ))*((N : ℝ)+2*budget N H t*(1+Real.log (H : ℝ))) :=
      logarithmic_bound N H hH hHN t ht
    _ ≤ (2*(N : ℝ)/(H : ℝ))*((N : ℝ)+2*budget N H t*(1+Real.log (N : ℝ))) := by
      apply mul_le_mul hfactor
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith : 1+Real.log (H : ℝ) ≤ 1+Real.log (N : ℝ))
          (mul_nonneg (by norm_num) (budget_nonneg N H t))))
        (add_nonneg (Nat.cast_nonneg N) (mul_nonneg
          (mul_nonneg (by norm_num) (budget_nonneg N H t)) (by linarith))) (by positivity)
    _ = _ := by
      unfold budget
      field_simp [hNr.ne',hHr.ne',abs_ne_zero.mpr ht]
      ring
end PaperP1.LogarithmicDifferencingBound
