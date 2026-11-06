module

public import PaperP1.Analysis.SeparatedPolynomialSampling

/-! # Centered logarithmic frequencies with exact norm invariance and bandwidth cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CenteredLogarithmicSampling
open Finset PaperP1 GaussianExponentialSums LogarithmicPhase GaussianFrequencyRowBound
open scoped Classical

theorem shift_polynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (c t : ℝ) :
    polynomial S a (fun n ↦ c+w n) t = phase c t * polynomial S a w t := by
  rw [polynomial, polynomial, mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [phase_add]
  ring

theorem shift_norm {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (c t : ℝ) :
    ‖polynomial S a (fun n ↦ c+w n) t‖ = ‖polynomial S a w t‖ := by
  rw [shift_polynomial, norm_mul, phase_norm, one_mul]

theorem logarithmic_bandwidth (L M n : ℝ) (hL : 0 < L) (hLn : L ≤ n) (hnM : n ≤ M) :
    |Real.log L-Real.log n| ≤ Real.log M-Real.log L := by
  have hlow := Real.log_le_log hL hLn
  have hupp := Real.log_le_log (hL.trans_le hLn) hnM
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

theorem integer_band_sampled_mean_square {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (S : Finset ℕ) (a : ℕ → ℂ) (L M : ℕ) (hL : 0 < L) (hM : 0 < M)
    (hS : ∀ n ∈ S, L ≤ n ∧ n ≤ M) :
    (∑ r ∈ R, ‖polynomial S a (fun n ↦ -Real.log n) (τ r)‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 2*Real.pi*(M : ℝ)) *
        (2+(Real.log M-Real.log L)^2) * ∑ n ∈ S, ‖a n‖^2 := by
  let w : ℕ → ℝ := fun n ↦ Real.log L-Real.log n
  have hgap : ∀ i ∈ S, ∀ j ∈ S, (1/(M : ℝ))*|(j : ℝ)-(i : ℝ)| ≤ |w j-w i| := by
    intro i hi j hj
    have hg := integer_log_gap M i j (hL.trans_le (hS i hi).1) (hL.trans_le (hS j hj).1)
      (hS i hi).2 (hS j hj).2
    have he : w j-w i = -(Real.log j-Real.log i) := by dsimp only [w]; ring
    rw [he, abs_neg]
    exact hg
  have hw : ∀ n ∈ S, |w n| ≤ Real.log M-Real.log L := by
    intro n hn
    exact logarithmic_bandwidth L M n (by exact_mod_cast hL)
      (by exact_mod_cast (hS n hn).1) (by exact_mod_cast (hS n hn).2)
  have hh := SeparatedPolynomialSampling.sampled_mean_square R τ T hT htau hsep S a w
    (1/(M : ℝ)) (Real.log M-Real.log L) (by positivity) hw hgap
  have he : 2*Real.pi/(1/(M : ℝ)) = 2*Real.pi*(M : ℝ) := by field_simp
  have hn (t : ℝ) : ‖polynomial S a w t‖ = ‖polynomial S a (fun n ↦ -Real.log n) t‖ :=
    shift_norm S a (fun n ↦ -Real.log n) (Real.log L) t
  simpa only [he,hn] using hh
end CenteredLogarithmicSampling
