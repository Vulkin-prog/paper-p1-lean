module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.LognormalSumIntegrability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PaperP1.Analysis.LognormalLowerTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalIntegralTails
open Finset Filter MeasureTheory PaperP1 LognormalSieveWeight
open scoped Classical

theorem lower_bound (A t N : ℝ) (hA : 0 < A) (hN : 0 ≤ N) :
    ‖∫ x in (0 : ℝ)..N, (weight A x : ℂ)*LogarithmicExponentialSum.function t x‖ ≤
      Real.exp 4*N^4/(4*A^3) := by
  have hG : IntervalIntegrable (fun x : ℝ ↦ Real.exp 4*x^3/A^3) volume 0 N := by
    have hc : Continuous (fun x : ℝ ↦ Real.exp 4*x^3/A^3) := by fun_prop
    exact hc.intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hN
    (f := fun x ↦ (weight A x : ℂ)*LogarithmicExponentialSum.function t x)
    (g := fun x ↦ Real.exp 4*x^3/A^3)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A x),LogarithmicExponentialSum.function_norm,mul_one]
      exact LognormalLowerTail.weight_bound A x hA hx.1)) hG
  have he : (∫ x in (0 : ℝ)..N, Real.exp 4*x^3/A^3)=Real.exp 4*N^4/(4*A^3) := by
    rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_pow]
    norm_num
    ring
  exact hh.trans_eq he

theorem sqrt_cutoff_bound (A t : ℝ) (hA : 1 ≤ A) :
    ‖∫ x in (0 : ℝ)..(⌈Real.sqrt A⌉₊ : ℝ), (weight A x : ℂ)*LogarithmicExponentialSum.function t x‖ ≤
      4*Real.exp 4/A := by
  have hAP : 0 < A := by linarith only [hA]
  have hS1 : 1 ≤ Real.sqrt A := by
    have hh := Real.sqrt_le_sqrt hA
    simpa only [Real.sqrt_one] using hh
  have hCut : (⌈Real.sqrt A⌉₊ : ℝ) ≤ 2*Real.sqrt A := by
    have hh := (Nat.ceil_lt_add_one (Real.sqrt_nonneg A)).le
    linarith only [hh,hS1]
  have hPower := pow_le_pow_left₀ (Nat.cast_nonneg ⌈Real.sqrt A⌉₊) hCut 4
  have hS4 : (2*Real.sqrt A)^4=16*A^2 := by
    calc
      _ = 16*((Real.sqrt A)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hAP.le]
  rw [hS4] at hPower
  calc
    _ ≤ Real.exp 4*(⌈Real.sqrt A⌉₊ : ℝ)^4/(4*A^3) := lower_bound A t _ hAP (Nat.cast_nonneg _)
    _ ≤ Real.exp 4*(16*A^2)/(4*A^3) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPower (Real.exp_pos 4).le) (by positivity)
    _ = _ := by field_simp [hAP.ne']; norm_num

theorem upper_bound (A t M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ‖∫ x in Set.Ioi M, (weight A x : ℂ)*LogarithmicExponentialSum.function t x‖ ≤
      Real.exp 1*A^3/(2*M^2) := by
  have hF : IntegrableOn (fun x : ℝ ↦ (weight A x : ℂ)*LogarithmicExponentialSum.function t x) (Set.Ioi M) :=
    (LognormalSumIntegrability.integrand_integrable A t hA).mono_set (fun x hx ↦ hM.trans hx)
  have hGBase := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hM
  have hG := hGBase.const_mul (Real.exp 1*A^3)
  have hDom : ∀ᵐ x ∂(volume.restrict (Set.Ioi M)),
      ‖(weight A x : ℂ)*LogarithmicExponentialSum.function t x‖ ≤ Real.exp 1*A^3*x^(-3 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxP : 0 < x := hM.trans hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A x),LogarithmicExponentialSum.function_norm,mul_one]
    have he : x^(-3 : ℝ)=1/x^3 := by norm_num [Real.rpow_neg hxP.le,Real.rpow_ofNat,one_div]
    rw [he,mul_one_div]
    exact polynomial_tail_bound A x hA hxP
  have hMono := integral_mono_ae hF.norm hG hDom
  have he : (∫ x in Set.Ioi M, Real.exp 1*A^3*x^(-3 : ℝ))=Real.exp 1*A^3/(2*M^2) := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hM]
    norm_num [Real.rpow_neg hM.le,Real.rpow_two]
    ring
  exact (norm_integral_le_integral_norm _).trans (hMono.trans_eq he)

theorem square_cutoff_bound (A t : ℝ) (hA : 0 < A) :
    ‖∫ x in Set.Ioi (⌈A^2⌉₊ : ℝ), (weight A x : ℂ)*LogarithmicExponentialSum.function t x‖ ≤
      Real.exp 1/(2*A) := by
  have hCut : 0 < (⌈A^2⌉₊ : ℝ) := (sq_pos_of_pos hA).trans_le (Nat.le_ceil (A^2))
  have hPower := pow_le_pow_left₀ (sq_nonneg A) (Nat.le_ceil (A^2)) 2
  calc
    _ ≤ Real.exp 1*A^3/(2*(⌈A^2⌉₊ : ℝ)^2) := upper_bound A t _ hA hCut
    _ ≤ Real.exp 1*A^3/(2*(A^2)^2) := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hPower (by norm_num))
    _ = _ := by field_simp [hA.ne']
end PaperP1.LognormalIntegralTails
