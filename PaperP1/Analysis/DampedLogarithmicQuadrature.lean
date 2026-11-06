module

public import PaperP1.Analysis.ReciprocalSquareTail
public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.DampedLogarithmicIntegral

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedLogarithmicQuadrature
open Finset Filter MeasureTheory PaperP1 DampedLogarithmicIntegral
open scoped Classical

theorem denominator_norm_upper (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖denominator σ t‖ ≤ σ+|t| := by
  have hh := norm_sub_le (-(σ : ℂ)) (Complex.I*(t : ℂ))
  simpa only [denominator,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσ,
    norm_mul,Complex.norm_I,one_mul] using hh

theorem hasDerivAt_integrand (σ t x : ℝ) (hx : 0 < x) :
    HasDerivAt (integrand σ t)
      ((denominator σ t-1)*numerator σ t x/(x : ℂ)^2) x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hh := (hasDerivAt_numerator σ t x hx).div ((hasDerivAt_id x).ofReal_comp) hxC
  convert hh using 1
  · rfl
  · simp only [id_eq]
    unfold integrand
    push_cast
    field_simp [hxC]

theorem derivative_norm_bound (σ t x : ℝ) (hσ : 0 ≤ σ) (hx : 0 < x) :
    ‖(denominator σ t-1)*numerator σ t x/(x : ℂ)^2‖ ≤
      (1+σ+|t|)*x^(-σ)/x^2 := by
  have hD : ‖denominator σ t-1‖ ≤ 1+σ+|t| := by
    have hh := (norm_sub_le (denominator σ t) 1).trans
      (add_le_add (denominator_norm_upper σ t hσ) (le_refl ‖(1 : ℂ)‖))
    have hh' : ‖denominator σ t-1‖ ≤ σ+|t|+1 := by simpa only [norm_one] using hh
    linarith only [hh']
  rw [norm_div,norm_mul,numerator_norm σ t x hx,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hx.le _)) (sq_nonneg x)

theorem derivative_uniform_bound (σ t A x : ℝ) (hσ : 0 ≤ σ) (hA : 0 < A) (hAx : A ≤ x) :
    ‖(denominator σ t-1)*numerator σ t x/(x : ℂ)^2‖ ≤
      (1+σ+|t|)*A^(-σ)/A^2 := by
  have hx : 0 < x := hA.trans_le hAx
  have hPow := Real.rpow_le_rpow_of_nonpos hA hAx (neg_nonpos.mpr hσ)
  have hC : 0 ≤ 1+σ+|t| := by positivity
  calc
    _ ≤ (1+σ+|t|)*x^(-σ)/x^2 := derivative_norm_bound σ t x hσ hx
    _ ≤ (1+σ+|t|)*A^(-σ)/x^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hC) (sq_nonneg x)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hA)
      (pow_le_pow_left₀ hA.le hAx 2)

theorem local_variation (σ t A x : ℝ) (hσ : 0 ≤ σ) (hA : 0 < A)
    (hx : x ∈ Set.Icc A (A+1)) :
    ‖integrand σ t x-integrand σ t A‖ ≤ (1+σ+|t|)*A^(-σ)/A^2 := by
  have hder : ∀ y ∈ Set.Icc A (A+1), HasDerivWithinAt (integrand σ t)
      ((denominator σ t-1)*numerator σ t y/(y : ℂ)^2) (Set.Icc A (A+1)) y :=
    fun y hy ↦ (hasDerivAt_integrand σ t y (hA.trans_le hy.1)).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.Ico A (A+1),
      ‖(denominator σ t-1)*numerator σ t y/(y : ℂ)^2‖ ≤ (1+σ+|t|)*A^(-σ)/A^2 :=
    fun y hy ↦ derivative_uniform_bound σ t A y hσ hA hy.1
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound x hx
  have hLen : x-A ≤ 1 := by linarith only [hx.2]
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hLen (by positivity : 0 ≤ (1+σ+|t|)*A^(-σ)/A^2))

theorem unit_integral_error (σ t A : ℝ) (hσ : 0 ≤ σ) (hA : 0 < A) :
    ‖integrand σ t A-(∫ x in A..A+1, integrand σ t x)‖ ≤ (1+σ+|t|)*A^(-σ)/A^2 := by
  have hi : IntervalIntegrable (integrand σ t) volume A (A+1) :=
    (continuousOn_integrand σ t A (A+1) hA).intervalIntegrable_of_Icc (by linarith)
  have he : integrand σ t A-(∫ x in A..A+1, integrand σ t x)=
      ∫ x in A..A+1, integrand σ t A-integrand σ t x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : A ≤ A+1)
    (f := fun x ↦ integrand σ t A-integrand σ t x)
    (g := fun _ ↦ (1+σ+|t|)*A^(-σ)/A^2)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_sub_rev]
      exact local_variation σ t A x hσ hA ⟨hx.1.le,hx.2⟩)) intervalIntegrable_const
  simpa using hh

theorem finite_sum_integral_error (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖(∑ n ∈ Ico N M, integrand σ t n)-
      (∫ x in (N : ℝ)..(M : ℝ), integrand σ t x)‖ ≤
      2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ k ∈ Set.Ico N M, IntervalIntegrable (integrand σ t) volume (k : ℝ) ((k+1 : ℕ) : ℝ) := by
    intro k hk
    have hp : (0 : ℝ) < k := by exact_mod_cast (hN.trans_le hk.1)
    simpa only [Nat.cast_add,Nat.cast_one] using
      (continuousOn_integrand σ t k (k+1) hp).intervalIntegrable_of_Icc (by linarith : (k : ℝ) ≤ k+1)
  have hCells := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
    (f := integrand σ t) (a := fun n : ℕ ↦ (n : ℝ)) hNM hint
  have he : (∑ n ∈ Ico N M, integrand σ t n)-
      (∫ x in (N : ℝ)..(M : ℝ), integrand σ t x)=
      ∑ n ∈ Ico N M, (integrand σ t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), integrand σ t x)) := by
    rw [sum_sub_distrib,hCells]
  rw [he]
  have hSquare := ReciprocalSquareTail.finite_bound (N : ℝ) hNR (Ico N M)
    (fun n hn ↦ by exact_mod_cast (mem_Ico.mp hn).1)
  calc
    _ ≤ ∑ n ∈ Ico N M, ‖integrand σ t n-(∫ x in (n : ℝ)..((n+1 : ℕ) : ℝ), integrand σ t x)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ico N M, ((1+σ+|t|)*(N : ℝ)^(-σ))*(1/(n : ℝ)^2) := by
      apply sum_le_sum
      intro n hn
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have hnp : (0 : ℝ) < n := hNR.trans_le hnN
      have hu := unit_integral_error σ t n hσ hnp
      rw [← Nat.cast_one,← Nat.cast_add] at hu
      have hPow := Real.rpow_le_rpow_of_nonpos hNR hnN (neg_nonpos.mpr hσ)
      exact hu.trans (by
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 1+σ+|t|)) (sq_nonneg (n : ℝ))
        simpa only [Nat.cast_one,div_eq_mul_inv,one_mul] using hh)
    _ = ((1+σ+|t|)*(N : ℝ)^(-σ))*(∑ n ∈ Ico N M, 1/(n : ℝ)^2) := by rw [mul_sum]
    _ ≤ ((1+σ+|t|)*(N : ℝ)^(-σ))*(2/(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hSquare (by positivity)
    _ = _ := by ring

theorem finite_sum_norm_bound (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (σ t : ℝ) (hσ : 0 ≤ σ) (ht : t ≠ 0) :
    ‖∑ n ∈ Ico N M, integrand σ t n‖ ≤
      2*(N : ℝ)^(-σ)/|t|+2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hError := finite_sum_integral_error N M hN hNM σ t hσ
  have hIntegral := integral_norm_bound σ t N M hσ ht hNR hNMR
  have hh := norm_add_le
    ((∑ n ∈ Ico N M, integrand σ t n)-(∫ x in (N : ℝ)..(M : ℝ), integrand σ t x))
    (∫ x in (N : ℝ)..(M : ℝ), integrand σ t x)
  rw [sub_add_cancel] at hh
  exact hh.trans ((add_le_add hError hIntegral).trans_eq (by ring))
end PaperP1.DampedLogarithmicQuadrature
