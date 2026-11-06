module

public import PaperP1.Analysis.SeparatedIntervalBudget

/-! # Discrete mean-square and large-value counts for finite exponential polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedPolynomialSampling
open Finset PaperP1 PaperP1.GaussianExponentialSums PaperP1.LogarithmicPhase
  PaperP1.DirichletPolynomialMeanValue
open scoped Classical

theorem phase_hasDerivAt (w t : ℝ) :
    HasDerivAt (phase w) (phase w t * (Complex.I * (w : ℂ))) t := by
  change HasDerivAt (fun x : ℝ ↦ Complex.exp (Complex.I*(w : ℂ)*(x : ℂ)))
    (Complex.exp (Complex.I*(w : ℂ)*(t : ℂ))*(Complex.I*(w : ℂ))) t
  simpa only [id_eq, Complex.ofReal_one, mul_one] using
    (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I*(w : ℂ))).cexp

theorem polynomial_hasDerivAt (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (polynomial S a w)
      (polynomial S (fun n ↦ a n * (Complex.I*(w n : ℂ))) w t) t := by
  have hh := HasDerivAt.fun_sum (u := S) (fun n hn ↦ (phase_hasDerivAt (w n) t).const_mul (a n))
  convert hh using 1
  · rfl
  · apply sum_congr rfl
    intro n hn
    ring

theorem derivative_coefficient_budget (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (W : ℝ) (hw : ∀ n ∈ S, |w n| ≤ W) :
    (∑ n ∈ S, ‖a n * (Complex.I*(w n : ℂ))‖^2) ≤ W^2 * ∑ n ∈ S, ‖a n‖^2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, mul_pow]
  have hp := pow_le_pow_left₀ (abs_nonneg _) (hw n hn) 2
  nlinarith [sq_nonneg ‖a n‖]

theorem sampled_mean_square {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (δ W : ℝ) (hδ : 0 < δ) (hw : ∀ n ∈ S, |w n| ≤ W)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, δ * |(j : ℝ)-(i : ℝ)| ≤ |w j-w i|) :
    (∑ r ∈ R, ‖polynomial S a w (τ r)‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi/δ) *
        (2+W^2) * ∑ n ∈ S, ‖a n‖^2 := by
  let b : ℕ → ℂ := fun n ↦ a n * (Complex.I*(w n : ℂ))
  have hlocal := SeparatedIntervalBudget.sampled_square_bound R τ (-(T+1)) (T+1)
    (by linarith) (fun r hr ↦ by constructor <;> linarith [(htau r hr).1,(htau r hr).2])
    hsep (polynomial S a w) (polynomial S b w) (polynomial_continuous S a w)
    (polynomial_continuous S b w) (polynomial_hasDerivAt S a w)
  have hF := separated_interval_bound S a w (T+1) δ (by linarith) hδ hgap
  have hG := separated_interval_bound S b w (T+1) δ (by linarith) hδ hgap
  have hcoef := derivative_coefficient_budget S a w W hw
  have hC : 0 ≤ Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi/δ) := by positivity
  have hb := hG.trans (mul_le_mul_of_nonneg_left hcoef hC)
  calc
    _ ≤ 2*(∫ x in -(T+1)..T+1, ‖polynomial S a w x‖^2) +
        (∫ x in -(T+1)..T+1, ‖polynomial S b w x‖^2) := hlocal
    _ ≤ 2*(Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi/δ)*∑ n ∈ S, ‖a n‖^2) +
        Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi/δ)*(W^2*∑ n ∈ S, ‖a n‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hF (by norm_num)) hb
    _ = _ := by ring

theorem large_values_card {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (δ W : ℝ) (hδ : 0 < δ) (hw : ∀ n ∈ S, |w n| ≤ W)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, δ * |(j : ℝ)-(i : ℝ)| ≤ |w j-w i|)
    (V : ℝ) (hV : 0 < V) (hbig : ∀ r ∈ R, V ≤ ‖polynomial S a w (τ r)‖) :
    (R.card : ℝ) ≤
      (Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi/δ) *
        (2+W^2) * ∑ n ∈ S, ‖a n‖^2) / V^2 := by
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hbig r hr) 2)
  simp only [sum_const, nsmul_eq_mul] at hl
  apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
  exact hl.trans (sampled_mean_square R τ T hT htau hsep S a w δ W hδ hw hgap)
end SeparatedPolynomialSampling
