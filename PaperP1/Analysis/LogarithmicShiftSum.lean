module

public import PaperP1.Analysis.ShiftedCorrelations
public import PaperP1.Analysis.LogarithmicShiftIntegral
public import PaperP1.Analysis.LogarithmicShiftPhase

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicShiftSum
open Finset MeasureTheory PaperP1 LogarithmicShiftPhase
open scoped Classical

theorem local_variation (t h A x : ℝ) (hA : 0 < A) (hh : 0 ≤ h) (hx : x ∈ Set.Icc A (A+1)) :
    ‖function t h x-function t h A‖ ≤ |t| * h/A^2 := by
  have hder : ∀ y ∈ Set.Icc A (A+1), HasDerivWithinAt (function t h)
      (function t h y*((-Complex.I*(t : ℂ)*(h : ℂ))/((y : ℂ)*((y+h : ℝ) : ℂ)))) (Set.Icc A (A+1)) y := by
    intro y hy
    have hyp : 0 < y := hA.trans_le hy.1
    exact (hasDerivAt_function t h y hyp (by linarith)).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico A (A+1),
      ‖function t h y*((-Complex.I*(t : ℂ)*(h : ℂ))/((y : ℂ)*((y+h : ℝ) : ℂ)))‖ ≤ |t| * h/A^2 := by
    intro y hy
    have hyp : 0 < y := hA.trans_le hy.1
    rw [derivative_norm t h y hyp hh]
    have hprod : A^2 ≤ y*(y+h) := by
      have hs := pow_le_pow_left₀ hA.le hy.1 2
      have hhy := mul_nonneg hyp.le hh
      nlinarith
    exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg t) hh) (sq_pos_of_pos hA) hprod
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound x hx
  have hlen : x-A ≤ 1 := by linarith [hx.2]
  exact hm.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ |t| * h/A^2))

theorem unit_integral_error (t h A : ℝ) (hA : 0 < A) (hh : 0 ≤ h) :
    ‖function t h A-(∫ x in A..A+1, function t h x)‖ ≤ |t| * h/A^2 := by
  have hc := LogarithmicShiftIntegral.continuousOn_function t h A (A+1) hA hh
  have hi : IntervalIntegrable (function t h) volume A (A+1) := hc.intervalIntegrable_of_Icc (by linarith)
  have he : function t h A-(∫ x in A..A+1, function t h x)=
      ∫ x in A..A+1, function t h A-function t h x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [he]
  have hm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : A ≤ A+1)
    (f := fun x ↦ function t h A-function t h x) (g := fun _ ↦ |t| * h/A^2)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_sub_rev]
      exact local_variation t h A x hA hh ⟨hx.1.le,hx.2⟩)) intervalIntegrable_const
  simpa using hm

theorem sum_integral_error (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hMN : M ≤ 2*N)
    (t h : ℝ) (hh : 0 ≤ h) :
    ‖(∑ n ∈ Ico N M, function t h n)-(∫ x in (N : ℝ)..(M : ℝ), function t h x)‖ ≤ |t| * h/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ k ∈ Set.Ico N M, IntervalIntegrable (function t h) volume (k : ℝ) ((k+1 : ℕ) : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hN.trans_le hk.1
    simpa only [Nat.cast_add,Nat.cast_one] using
      (LogarithmicShiftIntegral.continuousOn_function t h k (k+1) hkpos hh).intervalIntegrable_of_Icc (by linarith : (k : ℝ) ≤ k+1)
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := function t h)
    (a := fun n : ℕ ↦ (n : ℝ)) hNM hint
  have he : (∑ n ∈ Ico N M, function t h n)-(∫ x in (N : ℝ)..(M : ℝ), function t h x)=
      ∑ n ∈ Ico N M, (function t h n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function t h x)) := by
    rw [sum_sub_distrib,hs]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Ico N M, ‖function t h n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function t h x)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ico N M, |t| * h/(N : ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have hu := unit_integral_error t h (n : ℝ) (hNr.trans_le hnN) hh
      rw [← Nat.cast_one,← Nat.cast_add] at hu
      exact hu.trans (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hNr)
        (pow_le_pow_left₀ hNr.le hnN 2))
    _ = ((M-N : ℕ) : ℝ)*(|t| * h/(N : ℝ)^2) := by simp
    _ ≤ (N : ℝ)*(|t| * h/(N : ℝ)^2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show M-N ≤ N by omega)) (by positivity)
    _ = _ := by field_simp

theorem exponential_sum_bound (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hMN : M ≤ 2*N)
    (t h : ℝ) (ht : t ≠ 0) (hh : 0 < h) (hhN : h ≤ N) :
    ‖∑ n ∈ Ico N M, function t h n‖ ≤ 24*(N : ℝ)^2/(|t| * h)+|t| * h/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNMr : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hMNr : (M : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hMN
  have he := sum_integral_error N M hN hNM hMN t h hh.le
  have hi := LogarithmicShiftIntegral.integral_norm_bound t h N M ht hh hNr hNMr
  have hprod : 4*(M : ℝ)*((M : ℝ)+h) ≤ 24*(N : ℝ)^2 := by
    have hp := mul_le_mul hMNr (show (M : ℝ)+h ≤ 3*(N : ℝ) by linarith)
      (show 0 ≤ (M : ℝ)+h by positivity) (show 0 ≤ 2*(N : ℝ) by positivity)
    nlinarith
  have hib := hi.trans (div_le_div_of_nonneg_right hprod (by positivity))
  have hn : ‖∑ n ∈ Ico N M, function t h n‖ ≤
      ‖(∑ n ∈ Ico N M, function t h n)-(∫ x in (N : ℝ)..(M : ℝ), function t h x)‖+
      ‖∫ x in (N : ℝ)..(M : ℝ), function t h x‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      ((∑ n ∈ Ico N M, function t h n)-(∫ x in (N : ℝ)..(M : ℝ), function t h x))
      (∫ x in (N : ℝ)..(M : ℝ), function t h x)
  linarith

theorem correlation_identity (N d : ℕ) (hd : d ≤ N) (t : ℝ) :
    ShiftedCorrelations.correlation N (fun n ↦ LogarithmicExponentialSum.function t (N+n)) d=
      ∑ n ∈ Ico N (2*N-d), function t (d : ℝ) n := by
  rw [ShiftedCorrelations.correlation,sum_Ico_eq_sum_range]
  have hlen : 2*N-d-N=N-d := by omega
  rw [hlen]
  apply sum_congr rfl
  intro n hn
  simp only [function,Nat.cast_add,add_assoc]

theorem correlation_bound (N d : ℕ) (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N) (t : ℝ) (ht : t ≠ 0) :
    ‖ShiftedCorrelations.correlation N (fun n ↦ LogarithmicExponentialSum.function t (N+n)) d‖ ≤
      24*(N : ℝ)^2/(|t| * (d : ℝ))+|t| * (d : ℝ)/(N : ℝ) := by
  rw [correlation_identity N d hdN t]
  exact exponential_sum_bound N (2*N-d) hN (by omega) (by omega) t d ht
    (by exact_mod_cast hd) (by exact_mod_cast hdN)
end PaperP1.LogarithmicShiftSum
