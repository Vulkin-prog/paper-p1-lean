module

public import PaperP1.Analysis.GaussianCutoff

/-! # An actual finite Gaussian Perron formula with literal cutoff error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGaussianPerron
open Finset MeasureTheory PaperP1 GaussianLaplaceKernel GaussianCutoff LogarithmicPhase
open scoped Classical

def polynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i/(n i : ℂ)*phase (-Real.log (n i : ℝ)) t

def integrand {ι : Type*} (b X : ℝ) (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (t : ℝ) : ℂ :=
  (Real.exp (-b*t^2) : ℂ)*phase (Real.log X) t*polynomial S a n t/vertical t

def smoothed {ι : Type*} (b X : ℝ) (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) : ℂ :=
  ∑ i ∈ S, a i*(kernel b (Real.log (X/(n i : ℝ))) : ℂ)

def sharp {ι : Type*} (X : ℝ) (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) : ℂ :=
  ∑ i ∈ S, if (n i : ℝ) ≤ X then a i else 0

theorem integrand_expansion {ι : Type*} (b X : ℝ) (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (t : ℝ) :
    integrand b X S a n t=∑ i ∈ S, (a i/(n i : ℂ))*
      ((Real.exp (-b*t^2) : ℂ)*phase (Real.log X-Real.log (n i : ℝ)) t/vertical t) := by
  unfold integrand polynomial
  simp only [div_eq_mul_inv,mul_sum,sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [sub_eq_add_neg,phase_add]
  ring

theorem integrand_integrable {ι : Type*} (b X : ℝ) (hb : 0 < b)
    (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) : Integrable (integrand b X S a n) := by
  have hh := integrable_finsetSum S (fun i hi ↦
    (raw_integrable b (Real.log X-Real.log (n i : ℝ)) hb).const_mul (a i/(n i : ℂ)))
  exact hh.congr (Filter.Eventually.of_forall (fun t ↦ (integrand_expansion b X S a n t).symm))

theorem integral_expansion {ι : Type*} (b X : ℝ) (hb : 0 < b)
    (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) :
    (∫ t : ℝ, integrand b X S a n t)=∑ i ∈ S, (a i/(n i : ℂ))*rawKernel b (Real.log X-Real.log (n i : ℝ)) := by
  simp_rw [integrand_expansion]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    rfl
  · intro i hi
    exact (raw_integrable b (Real.log X-Real.log (n i : ℝ)) hb).const_mul _

theorem finite_formula {ι : Type*} (b X : ℝ) (hb : 0 < b) (hX : 0 < X)
    (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    smoothed b X S a n=((X/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, integrand b X S a n t) := by
  rw [integral_expansion b X hb S a n,mul_sum]
  unfold smoothed
  apply sum_congr rfl
  intro i hi
  have hnR : (0 : ℝ) < n i := by exact_mod_cast hn i hi
  rw [kernel_complex_formula b _ hb,Real.exp_log (div_pos hX hnR),Real.log_div hX.ne' hnR.ne']
  push_cast
  ring

theorem step_eq_indicator (X : ℝ) (m : ℕ) (hX : 0 < X) (hm : 0 < m) :
    step (Real.log (X/(m : ℝ)))=(if (m : ℝ) ≤ X then 1 else 0) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : 0 ≤ Real.log (X/(m : ℝ)) ↔ (m : ℝ) ≤ X :=
    (Real.log_nonneg_iff (div_pos hX hmR)).trans (one_le_div hmR)
  simp only [step,hi]

theorem sharp_as_step {ι : Type*} (X : ℝ) (hX : 0 < X) (S : Finset ι)
    (a : ι → ℂ) (n : ι → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    sharp X S a n=∑ i ∈ S, a i*(step (Real.log (X/(n i : ℝ))) : ℂ) := by
  unfold sharp
  apply sum_congr rfl
  intro i hi
  rw [step_eq_indicator X (n i) hX (hn i hi)]
  by_cases hc : (n i : ℝ) ≤ X
  · simp only [hc,ite_true,Complex.ofReal_one,mul_one]
  · simp only [hc,ite_false,Complex.ofReal_zero,mul_zero]

theorem cutoff_error {ι : Type*} (b X : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hX : 0 < X)
    (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    ‖smoothed b X S a n-sharp X S a n‖ ≤
      (Real.exp b-1)*(∑ i ∈ S.filter (fun i ↦ (n i : ℝ) ≤ X), ‖a i‖)+
        2*Real.exp b*(∑ i ∈ S, ‖a i‖*Real.exp (-(Real.log (X/(n i : ℝ)))^2/(32*b))) := by
  have he : smoothed b X S a n-sharp X S a n=∑ i ∈ S,
      a i * ((kernel b (Real.log (X/(n i : ℝ)))-step (Real.log (X/(n i : ℝ))) : ℝ) : ℂ) := by
    rw [sharp_as_step X hX S a n hn,smoothed,← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [he]
  have hpoint (i : ι) (hi : i ∈ S) :
      ‖a i * ((kernel b (Real.log (X/(n i : ℝ)))-step (Real.log (X/(n i : ℝ))) : ℝ) : ℂ)‖ ≤
      ‖a i‖*((if (n i : ℝ) ≤ X then Real.exp b-1 else 0)+
        2*Real.exp b*Real.exp (-(Real.log (X/(n i : ℝ)))^2/(32*b))) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hnR : (0 : ℝ) < n i := by exact_mod_cast hn i hi
    have hc : 0 ≤ Real.log (X/(n i : ℝ)) ↔ (n i : ℝ) ≤ X :=
      (Real.log_nonneg_iff (div_pos hX hnR)).trans (one_le_div hnR)
    exact mul_le_mul_of_nonneg_left (by simpa only [hc] using step_error b (Real.log (X/(n i : ℝ))) hb hb1) (norm_nonneg _)
  calc
    _ ≤ ∑ i ∈ S, ‖a i * ((kernel b (Real.log (X/(n i : ℝ)))-step (Real.log (X/(n i : ℝ))) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ‖a i‖*((if (n i : ℝ) ≤ X then Real.exp b-1 else 0)+
        2*Real.exp b*Real.exp (-(Real.log (X/(n i : ℝ)))^2/(32*b))) := sum_le_sum hpoint
    _ = _ := by
      rw [sum_filter]
      simp only [mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      by_cases hc : (n i : ℝ) ≤ X
      · simp only [hc,ite_true]; ring
      · simp only [hc,ite_false]; ring

theorem polynomial_continuous {ι : Type*} (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) :
    Continuous (polynomial S a n) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (phase_continuous _)

theorem integrand_norm {ι : Type*} (b X : ℝ) (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (t : ℝ) :
    ‖integrand b X S a n t‖=Real.exp (-b*t^2)*‖polynomial S a n t‖/Real.sqrt (1+t^2) := by
  simp only [integrand,norm_div,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),vertical_norm]

theorem smoothed_norm_bound {ι : Type*} (b X : ℝ) (hb : 0 < b) (hX : 0 < X)
    (S : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    ‖smoothed b X S a n‖ ≤ (X/(2*Real.pi))*(∫ t : ℝ,
      Real.exp (-b*t^2)*‖polynomial S a n t‖/Real.sqrt (1+t^2)) := by
  rw [finite_formula b X hb hX S a n hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < X/(2*Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [integrand_norm] using norm_integral_le_integral_norm (integrand b X S a n)
end PaperP1.FiniteGaussianPerron

