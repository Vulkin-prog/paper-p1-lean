module

public import PaperP1.Analysis.FirstGoodFullPolynomial
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.ActualIntermediateFrequencyRegion
public import PaperP1.Analysis.MixedEnvelopeLimit
public import PaperP1.Analysis.MixedRegionEnvelope

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntermediateContributionSmall
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

theorem rectangle_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualIntermediateFrequencyRegion.region N f T,
        ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
          (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨N₁,hN₁,hRect⟩ := ActualIntermediateFrequencyRegion.rectangle_bound
  obtain ⟨N₂,hN₂,hLim⟩ := MixedEnvelopeLimit.small_uniform ε hε
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  obtain ⟨NX,hX⟩ := eventually_atTop.mp (SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2))
  obtain ⟨NH,hH⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop 2))
  refine ⟨max N₁ (max N₂ (max NU (max NX NH))),by omega,?_⟩
  intro N hN f hf T hT hTN
  have hx := hX N (by omega)
  have hx0 : 0 ≤ SlowPrimeBandSieve.lower N := by linarith only [hx]
  have hcap : (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 :=
    Nat.floor_le (pow_nonneg hx0 3)
  have hEnvelope := MixedRegionEnvelope.envelope_bound N (GrowingFirstGoodRegion.width N)
    (hH N (by omega)) hx (hU N (by omega)) hcap
  exact (hRect N (by omega) f hf T hT hTN).trans (hEnvelope.trans (hLim N (by omega)))

theorem full_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualIntermediateFrequencyRegion.region N f T,
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨NR,hNR,hRect⟩ := rectangle_small_uniform (ε/4) (by positivity)
  obtain ⟨H₀,hH₀,NA,hNA,hApprox⟩ := TwoBandRectangleApproximation.both_rectangles_small_uniform (ε/4) (by positivity)
  obtain ⟨NH,hH⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop H₀))
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max NR (max NA (max NH NU)),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  have hlog1 : 1 ≤ Real.log (N : ℝ) := hU N (by omega)
  have hlog : 0 < Real.log (N : ℝ) := by linarith only [hlog1]
  have hTX : T ≤ N := hTN.trans ((div_le_iff₀ hlog).mpr (by
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [hlog1,hNN]))
  have hwide : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 := by
    intro n hn
    exact hb n (hNp.trans_le (mem_Ico.mp hn).1)
  have ha := (hApprox (GrowingFirstGoodRegion.width N) (hH N (by omega)) N (by omega) f hf hwide T hT hTX).2
  have hr := hRect N (by omega) f hb T hT hTN
  have hh := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _)
    (ActualIntermediateFrequencyRegion.region N f T)
    (ActualIntermediateFrequencyRegion.region_measurable N f T) T hT.le (fun _t ht ↦ ht.1)
  linarith only [hh,ha,hr]
end PaperP1.IntermediateContributionSmall
