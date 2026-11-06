module

public import PaperP1.Analysis.GaussianFibreError
public import PaperP1.Analysis.EulerFrequencyTruncation
public import PaperP1.Analysis.LogarithmicGaussianTail
public import PaperP1.Analysis.QuantitativeTriplePerron

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.WeightedPerronError
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def smoothingConstant : ℝ := (1/Real.log 2)*(2+2*Real.exp 1*(512*LogarithmicGaussianSum.constant))

def smoothingMajorant (X : ℕ) : ℝ := smoothingConstant*
  (((Real.log (X : ℝ))⁻¹)^4+((Real.log (X : ℝ))⁻¹)^6+
    ((Real.log (X : ℝ))^4+(Real.log (X : ℝ))^2)/(X : ℝ))

theorem error_nonneg (X : ℕ) : 0 ≤ QuantitativeTriplePerron.error X := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 ≤ LogarithmicGaussianSum.width X := by dsimp only [LogarithmicGaussianSum.width]; positivity
  have he : 0 ≤ Real.exp ((LogarithmicGaussianSum.width X)^2)-1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (sq_nonneg _))
  have hC := LogarithmicGaussianSum.constant_pos
  dsimp only [QuantitativeTriplePerron.error,GaussianFibreError.errorBound]
  positivity

theorem smoothingMajorant_tendsto : Tendsto smoothingMajorant atTop (nhds 0) := by
  have hnat : Tendsto (fun X : ℕ ↦ (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hnat
  have hi := tendsto_inv_atTop_zero.comp hlog
  have h4 : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))^4/(X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Real.rpow_ofNat,Function.comp_def] using (PNT.tendsto_pow_log_div_pow_atTop 1 4 zero_lt_one).comp hnat
  have h2 : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))^2/(X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Real.rpow_two,Function.comp_def] using (PNT.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one).comp hnat
  have hc := (((hi.pow 4).add (hi.pow 6)).add (h4.add h2)).const_mul smoothingConstant
  change Tendsto (fun X : ℕ ↦ smoothingConstant*
    (((Real.log (X : ℝ))⁻¹)^4+((Real.log (X : ℝ))⁻¹)^6+
      ((Real.log (X : ℝ))^4+(Real.log (X : ℝ))^2)/(X : ℝ))) atTop (nhds 0)
  simpa only [Function.comp_def,zero_pow (by decide : (4 : ℕ) ≠ 0),zero_pow (by decide : (6 : ℕ) ≠ 0),
    zero_add,mul_zero,add_div] using hc

theorem smoothing_bound_eventually :
    ∀ᶠ X : ℕ in atTop, ((Real.log (X : ℝ))^2/(X : ℝ))*QuantitativeTriplePerron.error X ≤ smoothingMajorant X := by
  filter_upwards [eventually_ge_atTop 2,
    LogarithmicGaussianSum.width_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))] with X hX hhalf
  have hδ := LogarithmicGaussianSum.width_positive X hX
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc := GaussianFibreError.errorBound_coarse (1/Real.log 2) (by positivity) X (LogarithmicGaussianSum.width X) hδ hhalf.le
  have hmul := mul_le_mul_of_nonneg_left hc
    (div_nonneg (sq_nonneg (Real.log (X : ℝ))) (Nat.cast_nonneg X))
  have hXP : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  have hlog : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
  calc
    _ ≤ ((Real.log (X : ℝ))^2/(X : ℝ))*((1/Real.log 2)*(2+2*Real.exp 1*(512*LogarithmicGaussianSum.constant))*
        ((Real.log (X : ℝ))^2+1)*(LogarithmicGaussianSum.width X*(X : ℝ)+1)) := hmul
    _ = _ := by
      dsimp only [smoothingMajorant,smoothingConstant,LogarithmicGaussianSum.width]
      field_simp [hXP,hlog]

theorem weighted_smoothing_tendsto :
    Tendsto (fun X : ℕ ↦ ((Real.log (X : ℝ))^2/(X : ℝ))*QuantitativeTriplePerron.error X) atTop (nhds 0) := by
  exact squeeze_zero' (Filter.Eventually.of_forall (fun X ↦
    mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg X)) (error_nonneg X)))
    smoothing_bound_eventually smoothingMajorant_tendsto


theorem weighted_tail_tendsto :
    Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))^2*EulerFrequencyTruncation.scaledTail X) atTop (nhds 0) := by
  have hnat : Tendsto (fun X : ℕ ↦ (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hnat
  have hC := FullEulerBound.eulerConstant_pos
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlim : Tendsto (fun X : ℕ ↦ ((FullEulerBound.eulerConstant/Real.log 2)*LogarithmicGaussianTail.constant)*
      (Real.log (X : ℝ))^13/(X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Real.rpow_ofNat,Function.comp_def,mul_zero,mul_div_assoc] using
      ((PNT.tendsto_pow_log_div_pow_atTop 1 13 zero_lt_one).comp hnat).const_mul
        ((FullEulerBound.eulerConstant/Real.log 2)*LogarithmicGaussianTail.constant)
  have hb : ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ))^2*EulerFrequencyTruncation.scaledTail X ≤
        ((FullEulerBound.eulerConstant/Real.log 2)*LogarithmicGaussianTail.constant)*(Real.log (X : ℝ))^13/(X : ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hlog.eventually (eventually_ge_atTop (max 2 (Real.log 4+4)))] with X hX hl
    have he := LogarithmicGaussianTail.tailEnvelope_bound X hX hl
    have hh := mul_le_mul_of_nonneg_left he
      (mul_nonneg (sq_nonneg (Real.log (X : ℝ))) (div_nonneg hC.le htwo.le))
    calc
      _ = ((Real.log (X : ℝ))^2*(FullEulerBound.eulerConstant/Real.log 2))*LogarithmicGaussianTail.tailEnvelope X := by
        dsimp only [EulerFrequencyTruncation.scaledTail]
        ring
      _ ≤ ((Real.log (X : ℝ))^2*(FullEulerBound.eulerConstant/Real.log 2))*
          (LogarithmicGaussianTail.constant*(Real.log (X : ℝ))^11/(X : ℝ)) := hh
      _ = _ := by ring
  exact squeeze_zero' (Filter.Eventually.of_forall (fun X ↦
    mul_nonneg (sq_nonneg _) (EulerFrequencyTruncation.scaledTail_nonneg X))) hb hlim

def combinedError (X : ℕ) : ℝ := QuantitativeTriplePerron.error X+
  ((X : ℝ)/(2*Real.pi))*EulerFrequencyTruncation.scaledTail X

def weightedNormalized (X : ℕ) : ℝ := ((Real.log (X : ℝ))^2/(X : ℝ))*combinedError X

theorem combinedError_nonneg (X : ℕ) : 0 ≤ combinedError X :=
  add_nonneg (error_nonneg X) (mul_nonneg (by positivity) (EulerFrequencyTruncation.scaledTail_nonneg X))

theorem weightedNormalized_tendsto : Tendsto weightedNormalized atTop (nhds 0) := by
  have hlim : Tendsto (fun X : ℕ ↦ ((Real.log (X : ℝ))^2/(X : ℝ))*QuantitativeTriplePerron.error X+
      (1/(2*Real.pi))*((Real.log (X : ℝ))^2*EulerFrequencyTruncation.scaledTail X)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using weighted_smoothing_tendsto.add (weighted_tail_tendsto.const_mul (1/(2*Real.pi)))
  have he : (fun X : ℕ ↦ ((Real.log (X : ℝ))^2/(X : ℝ))*QuantitativeTriplePerron.error X+
      (1/(2*Real.pi))*((Real.log (X : ℝ))^2*EulerFrequencyTruncation.scaledTail X))=ᶠ[atTop] weightedNormalized := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hn : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
    dsimp only [weightedNormalized,combinedError]
    field_simp [hn,Real.pi_ne_zero]
  exact hlim.congr' he

theorem weightedNormalized_small (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, weightedNormalized X ≤ ε := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (weightedNormalized_tendsto.eventually (eventually_lt_nhds hε))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX
  exact (hX₀ X ((le_max_left _ _).trans hX)).le
end PaperP1.WeightedPerronError
