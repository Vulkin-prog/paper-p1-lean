module

public import PaperP1.Analysis.IntermediateContributionSmall
public import PaperP1.Analysis.ScaledMixedPairEnergy


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ScaledIntermediateEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem envelope_bound (D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualIntermediateFrequencyRegion.region N f T,
        ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
          (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤
        (D+1)*MixedEnvelopeLimit.envelope N := by
  obtain ⟨NP,hNP,hPair⟩ := ScaledMixedPairEnergy.uniform_bound D hD
  have hGeometry : ∀ᶠ N : ℕ in atTop, 2 ≤ SlowPrimeBandSieve.lower N ∧ 1 ≤ SlowPrimeBandSieve.upper N ∧
      2 ≤ GrowingFirstGoodRegion.width N ∧ (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := by
    filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2),
      SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),GrowingFirstGoodRegion.width_geometry] with N hx hu hw
    exact ⟨hx,hu,hw.1,hw.2.1⟩
  obtain ⟨NG,hG⟩ := eventually_atTop.mp hGeometry
  refine ⟨max NP NG,by omega,?_⟩
  intro N hN f hf T hT hTime
  obtain ⟨hx,hu,hH,hCap⟩ := hG N (by omega)
  let H := GrowingFirstGoodRegion.width N
  let J := NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)
  let K := NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)
  let w (l : ℕ) := 2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor H l)^(-1/100 : ℝ)
  have hD1 : 0 ≤ D+1 := by linarith only [hD]
  have hC := BoundedAmplificationFactor.constant_pos
  have hPoint (j : ℕ) (hj : j ∈ J) (l : ℕ) (hl : l ∈ K) :
      (∫ t in ActualMixedPairDecay.region N j l f T, ‖ActualMixedPairDecay.term N l f t‖^2) ≤ (D+1)*w l := by
    have hh := hPair N (by omega) j hj l hl f hf T hT hTime
    have hQP := NarrowPrimeBands.anchor_pos H l
    have hNN : 0 ≤ (D+1)*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor H l)^(-1/100 : ℝ) := by positivity
    exact hh.trans (by dsimp only [w]; nlinarith only [hNN])
  have hh := FiniteFrequencyCover.finite_sum_cover_bound J K (fun l ↦ ActualMixedPairDecay.term N l f)
    (fun l _ ↦ ActualMixedPairDecay.term_continuous N l f) (ActualIntermediateFrequencyRegion.region N f T) T
    (fun j l ↦ ActualMixedPairDecay.region N j l f T) (fun l ↦ (D+1)*w l)
    (ActualIntermediateFrequencyRegion.region_measurable N f T) (fun _ ht ↦ ht.1)
    (fun j _ l _ ↦ ActualMixedPairDecay.region_measurable N j l f T)
    (fun _ _ _ _ _ ht ↦ ht.1) (fun l hl ↦ ActualIntermediateFrequencyRegion.cover_by_pairs N f T l hl) hPoint
  have hBase := MixedRegionEnvelope.envelope_bound N H hH hx hu hCap
  change (J.card : ℝ)*(K.card : ℝ)*(∑ l ∈ K, w l) ≤ MixedEnvelopeLimit.envelope N at hBase
  have hScale : (J.card : ℝ)*(K.card : ℝ)*(∑ l ∈ K, (D+1)*w l)=
      (D+1)*((J.card : ℝ)*(K.card : ℝ)*(∑ l ∈ K, w l)) := by rw [← mul_sum]; ring
  simp_rw [← ActualMixedPairDecay.sum_terms N f]
  exact hh.trans (hScale.le.trans (mul_le_mul_of_nonneg_left hBase hD1))

theorem rectangle_small_uniform (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualIntermediateFrequencyRegion.region N f T,
        ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
          (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := envelope_bound D hD
  have hLimit : Tendsto (fun N ↦ (D+1)*MixedEnvelopeLimit.envelope N) atTop (nhds 0) := by
    simpa only [mul_zero] using MixedEnvelopeLimit.envelope_tendsto.const_mul (D+1)
  obtain ⟨NE,hE⟩ := eventually_atTop.mp (hLimit.eventually (eventually_lt_nhds hε))
  refine ⟨max NB NE,by omega,?_⟩
  intro N hN f hf T hT hTime
  exact (hBound N (by omega) f hf T hT hTime).trans (hE N (by omega)).le

theorem full_small_uniform (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ m n, f (m*n)=f m*f n) → (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in ActualIntermediateFrequencyRegion.region N f T,
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨NR,hNR,hRectangle⟩ := rectangle_small_uniform D hD (ε/4) (by positivity)
  obtain ⟨H₀,hH₀,NA,hNA,hApprox⟩ := TwoBandRectangleApproximation.both_rectangles_small_uniform (ε/4) (by positivity)
  obtain ⟨NH,hWidth⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop H₀))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop (max 1 D)))
  refine ⟨max NR (max NA (max NH NL)),by omega,?_⟩
  intro N hN f hf hb T hT hTime
  have hNP : 0 < N := by omega
  have hLog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans (hLog N (by omega))
  have hDLog : D ≤ Real.log (N : ℝ) := (le_max_right _ _).trans (hLog N (by omega))
  have hLogP : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  have hTN : T ≤ (N : ℝ) := hTime.trans ((div_le_iff₀ hLogP).mpr (by
    have hh := mul_le_mul_of_nonneg_right hDLog (Nat.cast_nonneg N)
    nlinarith only [hh]))
  have hWide : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (hNP.trans_le (mem_Ico.mp hn).1)
  have ha := (hApprox (GrowingFirstGoodRegion.width N) (hWidth N (by omega)) N (by omega) f hf hWide T hT hTN).2
  have hr := hRectangle N (by omega) f hb T hT hTime
  have ht := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _) (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _)
    (ActualIntermediateFrequencyRegion.region N f T) (ActualIntermediateFrequencyRegion.region_measurable N f T)
    T hT.le (fun _ ht ↦ ht.1)
  linarith only [ht,ha,hr]
end PaperP1.ScaledIntermediateEnergy
