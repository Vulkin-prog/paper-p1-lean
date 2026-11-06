module

public import PaperP1.Analysis.GaussianCutoff

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianFrequencyTail
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def outside (T : ℝ) : Set ℝ := (Set.Ioc (-T) T)ᶜ

def tailBound (b T : ℝ) : ℝ := Real.exp (-b*T^2/2)*Real.sqrt (Real.pi/(b/2))

theorem outside_measurable (T : ℝ) : MeasurableSet (outside T) := measurableSet_Ioc.compl

theorem outside_square (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ outside T) : T^2 ≤ t^2 := by
  have hh : t ≤ -T ∨ T < t := by
    simpa only [outside,Set.mem_compl_iff,Set.mem_Ioc,not_and_or,not_lt,not_le] using ht
  rcases hh with hh | hh <;> nlinarith

theorem gaussian_point (b T : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ outside T) :
    Real.exp (-b*t^2) ≤ Real.exp (-b*T^2/2)*Real.exp (-(b/2)*t^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (outside_square T hT t ht) hb
  nlinarith

theorem gaussian_tail (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T) :
    (∫ t in outside T, Real.exp (-b*t^2)) ≤ tailBound b T := by
  have hi := integrable_exp_neg_mul_sq hb
  have hh := integrable_exp_neg_mul_sq (by positivity : 0 < b/2)
  have hm : (∫ t in outside T, Real.exp (-b*t^2)) ≤
      ∫ t in outside T, Real.exp (-b*T^2/2)*Real.exp (-(b/2)*t^2) := by
    apply integral_mono_ae hi.integrableOn (hh.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem (outside_measurable T)] with t ht
    exact gaussian_point b T hb.le hT t ht
  rw [integral_const_mul] at hm
  have hall := setIntegral_le_integral hh (Filter.Eventually.of_forall (fun t ↦ (Real.exp_pos _).le)) (s := outside T)
  calc
    _ ≤ Real.exp (-b*T^2/2)*(∫ t in outside T, Real.exp (-(b/2)*t^2)) := hm
    _ ≤ Real.exp (-b*T^2/2)*(∫ t : ℝ, Real.exp (-(b/2)*t^2)) := mul_le_mul_of_nonneg_left hall (Real.exp_pos _).le
    _ = _ := by rw [integral_gaussian]; rfl



theorem weighted_integrable (b : ℝ) (hb : 0 < b) (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ t : ℝ, 0 ≤ F t) (M : ℝ) (hbound : ∀ t : ℝ, F t ≤ M) :
    Integrable (fun t : ℝ ↦ Real.exp (-b*t^2)*F t) := by
  apply ((integrable_exp_neg_mul_sq hb).mul_const M).mono'
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).mul hF).aestronglyMeasurable
  filter_upwards [] with t
  change ‖Real.exp (-b*t^2)*F t‖ ≤ Real.exp (-b*t^2)*M
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hF0 t))]
  exact mul_le_mul_of_nonneg_left (hbound t) (Real.exp_pos _).le

theorem weighted_tail (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T) (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ t : ℝ, 0 ≤ F t) (M : ℝ) (hbound : ∀ t : ℝ, F t ≤ M) :
    (∫ t in outside T, Real.exp (-b*t^2)*F t) ≤ M*tailBound b T := by
  have hM : 0 ≤ M := (hF0 0).trans (hbound 0)
  have hm : (∫ t in outside T, Real.exp (-b*t^2)*F t) ≤ ∫ t in outside T, Real.exp (-b*t^2)*M := by
    apply integral_mono_ae (weighted_integrable b hb F hF hF0 M hbound).integrableOn
      ((integrable_exp_neg_mul_sq hb).mul_const M).integrableOn
    filter_upwards [] with t
    exact mul_le_mul_of_nonneg_left (hbound t) (Real.exp_pos _).le
  rw [integral_mul_const] at hm
  calc
    _ ≤ M*(∫ t in outside T, Real.exp (-b*t^2)) := by simpa only [mul_comm] using hm
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_tail b T hb hT) hM

theorem whole_integral_bound (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T) (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ t : ℝ, 0 ≤ F t) (M : ℝ) (hbound : ∀ t : ℝ, F t ≤ M) :
    (∫ t : ℝ, Real.exp (-b*t^2)*F t) ≤ (∫ t in -T..T, F t)+M*tailBound b T := by
  have hG : Continuous (fun t : ℝ ↦ Real.exp (-b*t^2)*F t) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).mul hF
  have hi := weighted_integrable b hb F hF hF0 M hbound
  have he := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hi
  have hmain : (∫ t in -T..T, Real.exp (-b*t^2)*F t) ≤ ∫ t in -T..T, F t := by
    apply intervalIntegral.integral_mono_on (by linarith) (hG.intervalIntegrable _ _) (hF.intervalIntegrable _ _)
    intro t ht
    have hh : Real.exp (-b*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (hF0 t)
  calc
    _ = (∫ t in -T..T, Real.exp (-b*t^2)*F t)+(∫ t in outside T, Real.exp (-b*t^2)*F t) := by
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact he.symm
    _ ≤ _ := add_le_add hmain (weighted_tail b T hb hT F hF hF0 M hbound)
end PaperP1.GaussianFrequencyTail
