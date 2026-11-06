module

public import PaperP1.Analysis.ActualNarrowMixedMean
public import PaperP1.Analysis.AmplificationThresholdDecay
public import PaperP1.Analysis.FloorAmplificationOrder
public import PaperP1.Analysis.ActualAnchorOrderGeometry

set_option autoImplicit false
@[expose] public noncomputable section
universe u805
namespace PaperP1.ActualMixedPairDecay
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

def region (N j l : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  MixedFrequencyAmplification.mixedSet
    (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f)
    (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f)
    T (FirstBandSmallRegion.threshold N) ((NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/40 : ℝ))

def term (N l : ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f t*
    DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N (GrowingFirstGoodRegion.width N) l)
      (NarrowRamareRectangle.coefficient (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f) t

theorem region_measurable (N j l : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (region N j l f T) :=
  MixedFrequencyAmplification.mixedSet_measurable _ _
    (GaussianExponentialSums.polynomial_continuous _ _ _) (GaussianExponentialSums.polynomial_continuous _ _ _) _ _ _

theorem term_continuous (N l : ℕ) (f : ℕ → ℂ) : Continuous (term N l f) :=
  (GaussianExponentialSums.polynomial_continuous _ _ _).mul (GaussianExponentialSums.polynomial_continuous _ _ _)

theorem sum_terms (N : ℕ) (f : ℕ → ℂ) (t : ℝ) :
    (∑ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N), term N l f t)=
      NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t := rfl

theorem estimates : ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
    ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      ∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      ∀ f : ℕ → ℂ, (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in region N j l f T, ‖term N l f t‖^2) ≤
        2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/100 : ℝ) ∧
      ∀ {ι : Type u805} (R : Finset ι) (τ : ι → ℝ),
        (∀ r ∈ R, τ r ∈ region N j l f T) →
        (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
        (∑ r ∈ R, ‖term N l f (τ r)‖^2) ≤
          54*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/100 : ℝ) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp ActualAnchorOrderGeometry.eventual_order_geometry
  refine ⟨max 1 NG,le_max_left _ _,?_⟩
  intro N hN j hj l hl f hf T hT hTN
  obtain ⟨hx,hH,hgeo⟩ := hG N (by omega)
  obtain ⟨hHu,huCap,hLogu,hLogu1,hq1,hLogq,hqLow,hkH,hkCap⟩ := hgeo j hj l hl
  let H := GrowingFirstGoodRegion.width N
  let x := SlowPrimeBandSieve.lower N
  let u := NarrowPrimeBands.anchor H j
  let q := NarrowPrimeBands.anchor H l
  let k := FloorAmplificationOrder.order u q
  let A := NarrowPrimeBands.band H (TwoPrimeBandPopulation.first N) j
  let Ltot := ⌈u⌉₊^k*⌈(N : ℝ)/q⌉₊
  have hu : 1 < u := by
    have hup : 0 < u := NarrowPrimeBands.anchor_pos H j
    have hh := Real.exp_lt_exp.mpr (show 0 < Real.log u by linarith only [hLogu1])
    simpa only [Real.exp_zero,Real.exp_log hup] using hh
  have hqp : 0 < q := NarrowPrimeBands.anchor_pos H l
  have hxp : 0 < x := by change 2 ≤ x at hx; linarith
  have hprime : ∀ p ∈ TwoPrimeBandPopulation.first N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hfP : ∀ p ∈ TwoPrimeBandPopulation.first N, ‖f p‖ ≤ 1 := fun p hp ↦ hf p (hprime p hp).pos
  have hfB : ∀ n ∈ NarrowRamareRectangle.cofactorSet N H l, ‖f n‖ ≤ 1 := by
    intro n hn
    have hh := (mem_Icc.mp (mem_filter.mp hn).1).1
    exact hf n (by omega)
  have hHReal : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hMass : (∑ p ∈ A, 1/(p : ℝ)) ≤ 1 := NarrowBandReciprocalMass.mass_le_one H hH
    (TwoPrimeBandPopulation.first N) (fun p hp ↦ (hprime p hp).one_le) j (by linarith only [hHReal,hHu])
  have hWeight : ((q^(-1/40 : ℝ))^2/(1/x^10)^(2*k))*AmplifiedPrimeProductMean.budget k A ≤ q^(-1/100 : ℝ) :=
    AmplificationThresholdDecay.mixed_weight_bound x u q hx hqp k hkCap A hMass hLogu
      (FloorAmplificationOrder.logarithmic_upper u q hu hq1)
  have hLength : T ≤ (Ltot : ℝ) := FloorAmplificationOrder.short_height_bound N u q T hu hq1 huCap hTN
  have hLp : (0 : ℝ) < Ltot := hT.trans_le hLength
  have hLnat : 0 < Ltot := by exact_mod_cast hLp
  have hL1 : (1 : ℝ) ≤ Ltot := by exact_mod_cast (show 1 ≤ Ltot by omega)
  have hRatio : T/(Ltot : ℝ)+1 ≤ 2 := by
    have hh := (div_le_one hLp).mpr hLength
    linarith only [hh]
  have hSampleRatio : (T+1)/(Ltot : ℝ)+1 ≤ 3 := by
    have hh : (T+1)/(Ltot : ℝ) ≤ 2 := (div_le_iff₀ hLp).mpr (by linarith only [hLength,hL1])
    linarith only [hh]
  have hv : 0 < 1/x^10 := by positivity
  have hw : 0 ≤ q^(-1/40 : ℝ) := Real.rpow_nonneg hqp.le _
  have hm := ActualNarrowMixedMean.estimates.{u805} N H j l k (by omega) hH hkH hHu
    (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N)
    hprime f hfP hfB T (1/x^10) (q^(-1/40 : ℝ)) hT hv hw
  let c := (q^(-1/40 : ℝ))^2/(1/x^10)^(2*k)
  change c*AmplifiedPrimeProductMean.budget k A ≤ q^(-1/100 : ℝ) at hWeight
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hb := AmplifiedPrimeProductMean.budget_nonneg k A
  have hScale (r R C : ℝ) (hr : r ≤ R) (hR : 0 ≤ R) (hC : 0 ≤ C) :
      c*(C*r*AmplifiedPrimeProductMean.budget k A) ≤ R*C*q^(-1/100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hr hWeight (mul_nonneg hc hb) hR) hC
    nlinarith only [hh]
  constructor
  · exact hm.1.trans (hScale _ 2 BoundedAmplificationFactor.constant hRatio (by norm_num) BoundedAmplificationFactor.constant_pos.le)
  · intro ι R τ hregion hsep
    have hh := hm.2 R τ hregion hsep
    have hs := hScale _ 3 (18*BoundedAmplificationFactor.constant) hSampleRatio (by norm_num)
      (mul_nonneg (by norm_num) BoundedAmplificationFactor.constant_pos.le)
    exact hh.trans (by convert hs using 1; ring)
end PaperP1.ActualMixedPairDecay
