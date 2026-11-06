module

public import PaperP1.Analysis.FixedEulerTruncation
public import PaperP1.Analysis.WeightedPrimeMean
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.EulerIntegralLimit
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def primeMass (P : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ p ∈ P, (Real.log (p : ℝ)/(p : ℝ))*‖a p‖

theorem primeMass_nonneg (P : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ primeMass P a :=
  sum_nonneg (fun p _ ↦ mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)) (norm_nonneg (a p)))

theorem prime_norm_bound (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖WeightedPrimeMean.value P a t‖ ≤ primeMass P a := by
  calc
    _ ≤ ∑ p ∈ P, ‖((Real.log (p : ℝ)/(p : ℝ) : ℝ) : ℂ)*a p‖ :=
      GaussianExponentialSums.polynomial_norm_bound P _ _ t
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))]

def weight (b : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (Q : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  Real.exp (-b*t^2)*‖WeightedPrimeMean.value P a t‖*‖WeightedPrimeMean.value Q c t‖/Real.sqrt (1+t^2)

theorem weight_nonneg (b : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (Q : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    0 ≤ weight b P a Q c t := by dsimp only [weight]; positivity

theorem sqrt_denominator_one (t : ℝ) : 1 ≤ Real.sqrt (1+t^2) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+t^2)
  have hn := Real.sqrt_nonneg (1+t^2)
  nlinarith [sq_nonneg t]

theorem weight_bound (b : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (Q : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    weight b P a Q c t ≤ (primeMass P a*primeMass Q c)*Real.exp (-b*t^2) := by
  have hroot : 0 < Real.sqrt (1+t^2) := by positivity
  have hprod := mul_le_mul (prime_norm_bound P a t) (prime_norm_bound Q c t)
    (norm_nonneg _) (primeMass_nonneg P a)
  have hleft := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-b*t^2)).le
  have hright := mul_le_mul_of_nonneg_left (sqrt_denominator_one t)
    (show 0 ≤ (primeMass P a*primeMass Q c)*Real.exp (-b*t^2) by
      exact mul_nonneg (mul_nonneg (primeMass_nonneg P a) (primeMass_nonneg Q c)) (Real.exp_pos _).le)
  apply (div_le_iff₀ hroot).mpr
  calc
    _ = Real.exp (-b*t^2)*(‖WeightedPrimeMean.value P a t‖*‖WeightedPrimeMean.value Q c t‖) := by ring
    _ ≤ Real.exp (-b*t^2)*(primeMass P a*primeMass Q c) := hleft
    _ ≤ _ := by nlinarith [hright]

theorem weight_continuous (b : ℝ) (P : Finset ℕ) (a : ℕ → ℂ) (Q : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (weight b P a Q c) := by
  exact (((Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).mul
    (WeightedPrimeMean.value_continuous P a).norm).mul (WeightedPrimeMean.value_continuous Q c).norm).div
    (continuous_const.add (continuous_id.pow 2)).sqrt (fun t ↦ by positivity)

theorem weight_integrable (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ) (Q : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (weight b P a Q c) := by
  apply ((integrable_exp_neg_mul_sq hb).const_mul (primeMass P a*primeMass Q c)).mono'
    (weight_continuous b P a Q c).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg b P a Q c t)]
  exact weight_bound b P a Q c t

theorem weighted_norm_integrable (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ)
    (Q : Finset ℕ) (c : ℕ → ℂ) (F : ℝ → ℂ) (hF : Continuous F)
    (M : ℝ) (hbound : ∀ t : ℝ, ‖F t‖ ≤ M) :
    Integrable (fun t : ℝ ↦ weight b P a Q c t*‖F t‖) := by
  apply ((weight_integrable b hb P a Q c).const_mul M).mono'
    ((weight_continuous b P a Q c).mul hF.norm).aestronglyMeasurable
  filter_upwards [] with t
  change ‖weight b P a Q c t*‖F t‖‖ ≤ M*weight b P a Q c t
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg b P a Q c t) (norm_nonneg _))]
  calc
    _ ≤ weight b P a Q c t*M := mul_le_mul_of_nonneg_left (hbound t) (weight_nonneg b P a Q c t)
    _ = _ := by ring



theorem truncated_integrable (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ)
    (Q : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (Y : ℕ) (f : ℕ → ℂ) (hf : ∀ n ∈ Nat.factoredNumbers E, ‖f n‖ ≤ 1) :
    Integrable (fun t : ℝ ↦ weight b P a Q c t*
      ‖FiniteGaussianPerron.polynomial (FixedEulerTruncation.support E Y) f id t‖) := by
  exact weighted_norm_integrable b hb P a Q c _ (FiniteGaussianPerron.polynomial_continuous _ _ _)
    (FixedEulerTruncation.majorant E) (FixedEulerTruncation.polynomial_norm_bound E hE Y f hf)

theorem total_integrable (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ)
    (Q : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ n ∈ Nat.factoredNumbers E, ‖f n‖ ≤ 1) :
    Integrable (fun t : ℝ ↦ weight b P a Q c t*‖FinitePrimeDirichletTruncation.total E f t‖) := by
  exact weighted_norm_integrable b hb P a Q c _ (FixedEulerTruncation.total_continuous E hE f hf)
    (FixedEulerTruncation.majorant E) (FixedEulerTruncation.total_norm_bound E hE f hf)

theorem integral_truncation_tendsto (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ)
    (Q : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ n ∈ Nat.factoredNumbers E, ‖f n‖ ≤ 1) :
    Tendsto (fun Y : ℕ ↦ ∫ t : ℝ, weight b P a Q c t*
      ‖FiniteGaussianPerron.polynomial (FixedEulerTruncation.support E Y) f id t‖) atTop
      (nhds (∫ t : ℝ, weight b P a Q c t*‖FinitePrimeDirichletTruncation.total E f t‖)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ FixedEulerTruncation.majorant E*weight b P a Q c t)
  · intro Y
    exact ((weight_continuous b P a Q c).mul (FiniteGaussianPerron.polynomial_continuous _ _ _).norm).aestronglyMeasurable
  · exact (weight_integrable b hb P a Q c).const_mul (FixedEulerTruncation.majorant E)
  · intro Y
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg b P a Q c t) (norm_nonneg _))]
    calc
      _ ≤ weight b P a Q c t*FixedEulerTruncation.majorant E :=
        mul_le_mul_of_nonneg_left (FixedEulerTruncation.polynomial_norm_bound E hE Y f hf t) (weight_nonneg b P a Q c t)
      _ = _ := by ring
  · filter_upwards [] with t
    exact tendsto_const_nhds.mul (FixedEulerTruncation.polynomial_tendsto E hE f hf t).norm
end PaperP1.EulerIntegralLimit
