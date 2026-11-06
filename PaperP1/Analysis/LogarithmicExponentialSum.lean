module

public import PaperP1.Analysis.GaussianExponentialSums
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual logarithmic exponential sums with a proved integral-comparison error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicExponentialSum
open Finset MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

def function (t x : ℝ) : ℂ := phase (-Real.log x) t

theorem function_norm (t x : ℝ) : ‖function t x‖=1 := phase_norm _ _

theorem hasDerivAt_function (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (function t) (function t x*((-Complex.I*(t : ℂ))/(x : ℂ))) x := by
  have he (y : ℝ) : function t y=Complex.exp ((-Complex.I*(t : ℂ))*(Real.log y : ℂ)) := by
    rw [function,phase,Complex.ofReal_neg]
    congr 1
    ring
  have hh := (((Real.hasDerivAt_log hx.ne').ofReal_comp).const_mul (-Complex.I*(t : ℂ))).cexp
  simp_rw [← he] at hh
  convert hh using 1
  push_cast
  ring

theorem derivative_norm (t x : ℝ) (hx : 0 < x) :
    ‖function t x*((-Complex.I*(t : ℂ))/(x : ℂ))‖=|t|/x := by
  rw [norm_mul,function_norm,one_mul,norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx]

theorem continuousOn_function (t A B : ℝ) (hA : 0 < A) :
    ContinuousOn (function t) (Set.Icc A B) := by
  intro x hx
  exact (hasDerivAt_function t x (hA.trans_le hx.1)).continuousAt.continuousWithinAt

theorem local_variation (t A x : ℝ) (hA : 0 < A) (hx : x ∈ Set.Icc A (A+1)) :
    ‖function t x-function t A‖ ≤ |t|/A := by
  have hder : ∀ y ∈ Set.Icc A (A+1),
      HasDerivWithinAt (function t) (function t y*((-Complex.I*(t : ℂ))/(y : ℂ))) (Set.Icc A (A+1)) y :=
    fun y hy ↦ (hasDerivAt_function t y (hA.trans_le hy.1)).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico A (A+1), ‖function t y*((-Complex.I*(t : ℂ))/(y : ℂ))‖ ≤ |t|/A := by
    intro y hy
    rw [derivative_norm t y (hA.trans_le hy.1)]
    exact div_le_div_of_nonneg_left (abs_nonneg t) hA hy.1
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound x hx
  have hxlen : x-A ≤ 1 := by linarith [hx.2]
  exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hxlen (by positivity : 0 ≤ |t|/A))

theorem unit_integral_error (t A : ℝ) (hA : 0 < A) :
    ‖function t A-(∫ x in A..A+1, function t x)‖ ≤ |t|/A := by
  have hc := continuousOn_function t A (A+1) hA
  have hi : IntervalIntegrable (function t) volume A (A+1) :=
    hc.intervalIntegrable_of_Icc (by linarith)
  have he : function t A-(∫ x in A..A+1, function t x) =
      ∫ x in A..A+1, function t A-function t x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : A ≤ A+1)
    (f := fun x ↦ function t A-function t x) (g := fun _ ↦ |t|/A)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_sub_rev]
      exact local_variation t A x hA ⟨hx.1.le,hx.2⟩)) intervalIntegrable_const
  simpa using hh

theorem sum_integral_error (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ‖(∑ n ∈ Ico N (2*N), function t n)-(∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x)‖ ≤ |t| := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ k ∈ Set.Ico N (2*N), IntervalIntegrable (function t) volume (k : ℝ) ((k+1 : ℕ) : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hN.trans_le hk.1
    simpa only [Nat.cast_add,Nat.cast_one] using
      (continuousOn_function t k (k+1) hkpos).intervalIntegrable_of_Icc (by linarith : (k : ℝ) ≤ k+1)
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := function t) (a := fun n : ℕ ↦ (n : ℝ))
    (by omega : N ≤ 2*N) hint
  have he : (∑ n ∈ Ico N (2*N), function t n)-(∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x) =
      ∑ n ∈ Ico N (2*N), (function t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function t x)) := by
    rw [sum_sub_distrib,hs]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Ico N (2*N), ‖function t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), function t x)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ico N (2*N), |t|/(N : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have hu := unit_integral_error t (n : ℝ) (hNr.trans_le hnN)
      rw [← Nat.cast_one,← Nat.cast_add] at hu
      exact hu.trans (div_le_div_of_nonneg_left (abs_nonneg t) hNr hnN)
    _ = |t| := by
      have hcard : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
      rw [sum_const,nsmul_eq_mul,hcard]
      field_simp

def primitive (t x : ℝ) : ℂ := (x : ℂ)*function t x/(1-Complex.I*(t : ℂ))

theorem denominator_ne (t : ℝ) : (1-Complex.I*(t : ℂ) : ℂ) ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh

theorem hasDerivAt_primitive (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (primitive t) (function t x) x := by
  have hh := ((hasDerivAt_id x).ofReal_comp.mul (hasDerivAt_function t x hx)).div_const (1-Complex.I*(t : ℂ))
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hc : (function t x+(x : ℂ)*(function t x*((-Complex.I*(t : ℂ))/(x : ℂ))))/
      (1-Complex.I*(t : ℂ))=function t x := by
    field_simp [hxC,denominator_ne t]
    ring
  change HasDerivAt (fun y : ℝ ↦ (y : ℂ)*function t y/(1-Complex.I*(t : ℂ))) (function t x) x
  simp only [id_eq,Complex.ofReal_one,one_mul,hc] at hh
  convert hh using 1

theorem interval_integral (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x) =
      primitive t ((2*N : ℕ) : ℝ)-primitive t N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : (N : ℝ) ≤ ((2*N : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2*N by omega)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact hasDerivAt_primitive t x (hNr.trans_le hx.1)
  · exact (continuousOn_function t N ((2*N : ℕ) : ℝ) hNr).intervalIntegrable_of_Icc hAB
theorem interval_integral_norm (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t ≠ 0) :
    ‖∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x‖ ≤ 3*(N : ℝ)/|t| := by
  rw [interval_integral N hN t,primitive,primitive,← sub_div,norm_div]
  have hnum : ‖(((2*N : ℕ) : ℂ)*function t ((2*N : ℕ) : ℝ))-(N : ℂ)*function t N‖ ≤ 3*(N : ℝ) := by
    calc
      _ ≤ ‖((2*N : ℕ) : ℂ)*function t ((2*N : ℕ) : ℝ)‖+‖(N : ℂ)*function t N‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul,norm_mul,function_norm,function_norm,Complex.norm_natCast,Complex.norm_natCast]; push_cast; ring
  have hsq : ‖1-Complex.I*(t : ℂ)‖^2=1+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp
    ring
  have hden : |t| ≤ ‖1-Complex.I*(t : ℂ)‖ := by
    nlinarith [sq_abs t,norm_nonneg (1-Complex.I*(t : ℂ)),abs_nonneg t]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr ht) hden)

theorem exponential_sum_bound (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N (2*N), function t n‖ ≤ 3*(N : ℝ)/|t|+|t| := by
  have he := sum_integral_error N hN t
  have hi := interval_integral_norm N hN t ht
  have hh : ‖∑ n ∈ Ico N (2*N), function t n‖ ≤
      ‖(∑ n ∈ Ico N (2*N), function t n)-(∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x)‖+
      ‖∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      ((∑ n ∈ Ico N (2*N), function t n)-(∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x))
      (∫ x in (N : ℝ)..((2*N : ℕ) : ℝ), function t x)
  linarith
end LogarithmicExponentialSum
