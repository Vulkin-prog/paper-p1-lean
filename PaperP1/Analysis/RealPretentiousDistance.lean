module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Arithmetic.PrimeAvoidanceSieve
public import PaperP1.Arithmetic.OrdinarySmoothIndicator
public import PaperP1.Asymptotics.SlowPrimeBandSieve

/-! # Finite real pretentious distance sums and exact phase repulsion

The function `distance` is the finite sum conventionally called the squared
pretentious distance; no square root is silently taken.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealPretentiousDistance
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums
open scoped Classical

def distance (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)

def phaseDefect (P : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, (1-Real.cos (t*Real.log p))/(p : ℝ)

theorem point_nonneg (u θ : ℝ) (hu : |u| ≤ 1) : 0 ≤ 1-u*Real.cos θ := by
  have hm : |u*Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hu (Real.abs_cos_le_one θ) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  linarith [le_abs_self (u*Real.cos θ)]

theorem point_upper (u θ : ℝ) (hu : |u| ≤ 1) : 1-u*Real.cos θ ≤ 2 := by
  have hm : |u*Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hu (Real.abs_cos_le_one θ) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  linarith [(abs_le.mp hm).1]

theorem point_repulsion (u θ : ℝ) (hu : |u| ≤ 1) : 1-Real.cos (2*θ) ≤ 4*(1-u*Real.cos θ) := by
  have hs : u^2 ≤ 1 := by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ-u)]

theorem distance_nonneg (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) : 0 ≤ distance P f t := by
  exact sum_nonneg (fun p hp ↦ div_nonneg (point_nonneg _ _ (hf p hp)) (Nat.cast_nonneg p))

theorem distance_upper (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) : distance P f t ≤ 2*PrimeAvoidanceSieve.reciprocalMass P := by
  unfold distance PrimeAvoidanceSieve.reciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hh := div_le_div_of_nonneg_right (point_upper (f p) (t*Real.log p) (hf p hp)) (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  simpa only [mul_one_div] using hh

theorem distance_even (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : distance P f (-t)=distance P f t := by
  simp only [distance,neg_mul,Real.cos_neg]

theorem real_repulsion (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) : phaseDefect P (2*t) ≤ 4*distance P f t := by
  unfold phaseDefect distance
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hh := div_le_div_of_nonneg_right (point_repulsion (f p) (t*Real.log p) (hf p hp))
    (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  simpa only [mul_assoc,mul_div_assoc] using hh

theorem phase_re (w t : ℝ) : (phase w t).re=Real.cos (w*t) := by
  simp [phase,Complex.exp_re]

theorem distance_eq_real_dirichlet (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) :
    distance P f t=PrimeAvoidanceSieve.reciprocalMass P-
      (DirichletPolynomialMeanValue.value P (fun p ↦ (f p : ℂ)) t).re := by
  unfold distance PrimeAvoidanceSieve.reciprocalMass DirichletPolynomialMeanValue.value polynomial
  rw [Complex.re_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  change (1-f p*Real.cos (t*Real.log p))/(p : ℝ)=
    1/(p : ℝ)-((f p : ℂ)/(p : ℂ)*phase (-Real.log p) t).re
  rw [← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,phase_re,neg_mul,Real.cos_neg]
  rw [mul_comm (Real.log p) t]
  ring

theorem distance_one_eq_phaseDefect (P : Finset ℕ) (t : ℝ) :
    distance P (fun _ ↦ 1) t=phaseDefect P t := by simp only [distance,phaseDefect,one_mul]

theorem phaseDefect_eq_mass_sub_re (P : Finset ℕ) (t : ℝ) :
    phaseDefect P t=PrimeAvoidanceSieve.reciprocalMass P-
      (DirichletPolynomialMeanValue.value P (fun _ ↦ 1) t).re := by
  simpa only [distance_one_eq_phaseDefect,Complex.ofReal_one] using distance_eq_real_dirichlet P (fun _ ↦ 1) t

theorem real_repulsion_norm_lower (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) :
    PrimeAvoidanceSieve.reciprocalMass P-‖DirichletPolynomialMeanValue.value P (fun _ ↦ 1) (2*t)‖ ≤
      4*distance P f t := by
  have hr := real_repulsion P f t hf
  rw [phaseDefect_eq_mass_sub_re] at hr
  have hn := Complex.re_le_norm (DirichletPolynomialMeanValue.value P (fun _ ↦ 1) (2*t))
  linarith

theorem real_close_implies_prime_large (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1)
    (hclose : distance P f t ≤ PrimeAvoidanceSieve.reciprocalMass P/8) :
    PrimeAvoidanceSieve.reciprocalMass P/2 ≤ ‖DirichletPolynomialMeanValue.value P (fun _ ↦ 1) (2*t)‖ := by
  have hr := real_repulsion_norm_lower P f t hf
  linarith

theorem smooth_prime_value (Y p : ℕ) (hp : p.Prime) :
    OrdinarySmoothIndicator.value Y p=if p ≤ Y then 1 else 0 := by
  simp only [OrdinarySmoothIndicator.value,ne_eq,hp.ne_zero,not_false_eq_true,true_and,
    OrdinarySmoothCensus.largestPrimeFactor_prime hp]

theorem smooth_distance_decomposition (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y : ℕ) (t : ℝ) :
    distance P (OrdinarySmoothIndicator.value Y) t = phaseDefect (P.filter (fun p ↦ p ≤ Y)) t+
      PrimeAvoidanceSieve.reciprocalMass (P.filter (fun p ↦ ¬p ≤ Y)) := by
  rw [distance,phaseDefect,PrimeAvoidanceSieve.reciprocalMass,sum_filter,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [smooth_prime_value Y p (hP p hp)]
  by_cases h : p ≤ Y <;> simp [h]

theorem smooth_band_distance_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ t : ℝ,
      distance (SlowPrimeBandSieve.primes N) (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊) t =
        phaseDefect (SlowPrimeBandSieve.primes N) t := by
  filter_upwards [SlowPrimeBandSieve.primes_below_polynomial_cutoff_eventually a ha] with N hcut t
  apply sum_congr rfl
  intro p hp
  rw [smooth_prime_value _ p (mem_filter.mp hp).2,ite_eq_left (hcut p hp),one_mul]
end RealPretentiousDistance
