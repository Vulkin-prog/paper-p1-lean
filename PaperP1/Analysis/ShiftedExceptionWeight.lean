module

public import PaperP1.Analysis.PrimeUnitMean
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import PaperP1.Analysis.FullEulerEnvelope
public import PaperP1.Analysis.ReciprocalFrequencyWeights
public import PaperP1.Analysis.UnitThickening

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ShiftedExceptionWeight
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem exceptional_subset (N K : ℕ) : FullEulerEnvelope.exceptional N K ⊆
    Set.Icc (-(K : ℝ)-1) ((K : ℝ)+1) :=
  UnitThickening.thickening_subset K _ (filter_subset _ _)

theorem indicator_integrable (N K : ℕ) :
    Integrable ((FullEulerEnvelope.exceptional N K).indicator (fun _ ↦ (1 : ℝ))) := by
  have hi : IntegrableOn (fun _t : ℝ ↦ (1 : ℝ)) (Set.Icc (-(K : ℝ)-1) ((K : ℝ)+1)) volume :=
    (continuous_const : Continuous (fun _t : ℝ ↦ (1 : ℝ))).integrableOn_Icc
  exact (integrable_indicator_iff (FullEulerEnvelope.exceptional_measurable N K)).mpr
    (hi.mono_set (exceptional_subset N K))

theorem integral_indicator (N K : ℕ) :
    (∫ t : ℝ, (FullEulerEnvelope.exceptional N K).indicator (fun _ ↦ (1 : ℝ)) t)=
      volume.real (FullEulerEnvelope.exceptional N K) := by
  rw [integral_indicator_const _ (FullEulerEnvelope.exceptional_measurable N K),smul_eq_mul,mul_one]

theorem shifted_indicator_interval (N K : ℕ) (c T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in -T..T, (FullEulerEnvelope.exceptional N K).indicator (fun _ ↦ (1 : ℝ)) (c+τ)) ≤
      volume.real (FullEulerEnvelope.exceptional N K) := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  calc
    _ ≤ ∫ τ : ℝ, (FullEulerEnvelope.exceptional N K).indicator (fun _ ↦ (1 : ℝ)) (c+τ) :=
      setIntegral_le_integral ((indicator_integrable N K).comp_add_left c)
        (Filter.Eventually.of_forall (fun τ ↦ Set.indicator_nonneg (fun _ _ ↦ by norm_num) _))
    _ = ∫ t : ℝ, (FullEulerEnvelope.exceptional N K).indicator (fun _ ↦ (1 : ℝ)) t := integral_add_left_eq_self _ c
    _ = _ := integral_indicator N K

theorem badWeight_measurable (N K M : ℕ) : Measurable (FullEulerEnvelope.badWeight N K M) := by
  apply Finset.measurable_sum
  intro j hj
  exact (((measurable_const.indicator (FullEulerEnvelope.exceptional_measurable N K)).comp
    (measurable_const.add measurable_id)).div_const (1+((j : ℝ)-(M : ℝ))^2))

theorem badWeight_integrable (N K M : ℕ) : Integrable (FullEulerEnvelope.badWeight N K M) := by
  apply integrable_finsetSum
  intro j hj
  exact ((indicator_integrable N K).comp_add_left ((j : ℝ)-(M : ℝ))).div_const (1+((j : ℝ)-(M : ℝ))^2)


theorem integral_badWeight (N K M : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in -T..T, FullEulerEnvelope.badWeight N K M τ) ≤
      5*volume.real (FullEulerEnvelope.exceptional N K) := by
  unfold FullEulerEnvelope.badWeight
  rw [intervalIntegral.integral_finsetSum (fun (j : ℕ) _hj ↦
    (((indicator_integrable N K).comp_add_left ((j : ℝ)-(M : ℝ))).div_const (1+((j : ℝ)-(M : ℝ))^2)).intervalIntegrable)]
  calc
    _ ≤ ∑ j ∈ range (2*M+1), volume.real (FullEulerEnvelope.exceptional N K)/(1+((j : ℝ)-(M : ℝ))^2) := by
      apply sum_le_sum
      intro j hj
      rw [intervalIntegral.integral_div]
      exact div_le_div_of_nonneg_right (shifted_indicator_interval N K ((j : ℝ)-(M : ℝ)) T hT) (by positivity)
    _ = volume.real (FullEulerEnvelope.exceptional N K)*(∑ j ∈ range (2*M+1), 1/(1+((j : ℝ)-(M : ℝ))^2)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (ReciprocalFrequencyWeights.finite_weight_bound (range (2*M+1)) M)
        (measureReal_nonneg : 0 ≤ volume.real (FullEulerEnvelope.exceptional N K))
      nlinarith

def largeShifts (N K M : ℕ) (T V : ℝ) : Set ℝ :=
  Set.Ioc (-T) T ∩ {τ : ℝ | V ≤ FullEulerEnvelope.badWeight N K M τ}

theorem largeShifts_measurable (N K M : ℕ) (T V : ℝ) : MeasurableSet (largeShifts N K M T V) :=
  measurableSet_Ioc.inter (measurableSet_le measurable_const (badWeight_measurable N K M))

theorem largeShifts_budget (N K M : ℕ) (T : ℝ) (hT : 0 ≤ T) (V : ℝ) :
    V*volume.real (largeShifts N K M T V) ≤ 5*volume.real (FullEulerEnvelope.exceptional N K) := by
  let μ := volume.restrict (Set.Ioc (-T) T)
  have : IsFiniteMeasure μ := ⟨by dsimp only [μ]; finiteness⟩
  have hint : Integrable (FullEulerEnvelope.badWeight N K M) μ := (badWeight_integrable N K M).integrableOn
  have hnonneg : 0 ≤ᵐ[μ] FullEulerEnvelope.badWeight N K M :=
    Filter.Eventually.of_forall (FullEulerEnvelope.badWeight_nonneg N K M)
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hint V
  have he : μ.real {τ : ℝ | V ≤ FullEulerEnvelope.badWeight N K M τ}=
      volume.real (largeShifts N K M T V) := by
    dsimp only [μ]
    rw [measureReal_restrict_apply (measurableSet_le measurable_const (badWeight_measurable N K M))]
    congr 1
    ext τ
    simp only [largeShifts,Set.mem_inter_iff,Set.mem_ofPred_eq,and_comm]
  rw [he] at hm
  have hb := integral_badWeight N K M T hT
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hb
  exact hm.trans hb

theorem largeShifts_measure (N K M : ℕ) (T : ℝ) (hT : 0 ≤ T) (V : ℝ) (hV : 0 < V) :
    volume.real (largeShifts N K M T V) ≤ 5*volume.real (FullEulerEnvelope.exceptional N K)/V := by
  apply (le_div_iff₀ hV).mpr
  have hb := largeShifts_budget N K M T hT V
  simpa only [mul_comm V] using hb

theorem off_largeShifts (N K M : ℕ) (T V τ : ℝ) (hτ : τ ∈ Set.Ioc (-T) T)
    (hnot : τ ∉ largeShifts N K M T V) : FullEulerEnvelope.badWeight N K M τ < V := by
  by_contra! hh
  exact hnot ⟨hτ,hh⟩
end PaperP1.ShiftedExceptionWeight
