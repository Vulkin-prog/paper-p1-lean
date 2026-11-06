module

public import PaperP1.Analysis.FinalPrimeBandPopulation
public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.FinalNarrowBandGeometry
public import PaperP1.Analysis.FiniteProductSampleBound
public import PaperP1.Analysis.JointLargeSparseCofactors

set_option autoImplicit false
@[expose] public noncomputable section
universe u837
namespace PaperP1.FinalSmallPrimeSamples
open Finset Filter PaperP1
open scoped Classical

def threshold (N : ℕ) : ℝ := 1/(SlowPrimeBandSieve.upper N)^100

def envelope (N : ℕ) : ℝ := 80/(SlowPrimeBandSieve.upper N)^191

theorem envelope_tendsto : Tendsto envelope atTop (nhds 0) := by
  change Tendsto (fun N ↦ 80/(SlowPrimeBandSieve.upper N)^191) atTop (nhds 0)
  have hh := ((tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.upper_tendsto).pow 191).const_mul 80
  simpa only [Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow (by norm_num : 191 ≠ 0),mul_zero] using hh

theorem scalar_bound (z c : ℝ) (hz : 1 ≤ z) (hc0 : 0 ≤ c) (hc : c ≤ 2*z^4) :
    c^2*(1/z^100)^2*(10*(1+z)) ≤ 80/z^191 := by
  have hzp : 0 < z := by linarith only [hz]
  have hSq := pow_le_pow_left₀ hc0 hc 2
  have hOne : 1+z ≤ 2*z := by linarith only [hz]
  calc
    _ ≤ (2*z^4)^2*(1/z^100)^2*(10*(2*z)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hSq (by positivity))
        (mul_le_mul_of_nonneg_left hOne (by norm_num : (0 : ℝ) ≤ 10)) (by positivity) (by positivity)
    _ = _ := by field_simp; ring

theorem sampled_rectangle_bound (B : ℕ) (hB : 32 ≤ B) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ {ι : Type u837} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f (τ r)‖ ≤ threshold N) →
      (∑ r ∈ R, ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
        (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f (τ r)‖^2) ≤ envelope N := by
  obtain ⟨NS,hNS,hSample⟩ := JointLargeSparseCofactors.cofactor_mean_uniform.{u837}
  have hGeometry : ∀ᶠ N : ℕ in atTop, 1 ≤ SlowPrimeBandSieve.upper N ∧
      1 ≤ GrowingFirstGoodRegion.width N ∧
      (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := by
    filter_upwards [SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),
      GrowingFirstGoodRegion.width_geometry] with N hz hw
    exact ⟨hz,by omega,hw.2.1⟩
  obtain ⟨NG,hG⟩ := eventually_atTop.mp hGeometry
  refine ⟨max NS NG,by omega,?_⟩
  intro N hN f hf ι R τ T hT hTN hInside hsep hSmall
  obtain ⟨hz,hH,hHcap⟩ := hG N (by omega)
  let H := GrowingFirstGoodRegion.width N
  let P := FinalPrimeBandGeometry.primes B N
  let Q := TwoPrimeBandPopulation.first N
  let J := NarrowPrimeBands.indices H P
  let A (j : ℕ) (r : ι) := DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r)
  let F (j : ℕ) (r : ι) := DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j)
    (NarrowRamareRectangle.coefficient P Q f) (τ r)
  have hfSecond : ∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1 := fun p hp ↦ hf p (mem_filter.mp hp).2.pos
  have hCof (j : ℕ) (hj : j ∈ J) : (∑ r ∈ R, ‖F j r‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
    have hAnchor := FinalNarrowBandGeometry.anchor_upper B N H j hB (by omega) (by omega) hj
    apply hSample N (by omega) f hfSecond R τ T hT hTN hInside hsep H j hAnchor P Q f
    intro n hn
    apply hf n
    have hh := (mem_Icc.mp (mem_filter.mp hn).1).1
    omega
  have hBound := FiniteProductSampleBound.bound J R A F (threshold N) (10*(1+Real.log (N : ℝ)))
    (fun j hj r hr ↦ hSmall r hr j hj) hCof
  have hCard := FinalNarrowBandGeometry.index_card_bound B N H hB (by omega) hz hHcap
  have hScalar := scalar_bound (SlowPrimeBandSieve.upper N) (J.card : ℝ) hz (Nat.cast_nonneg J.card) hCard
  change (J.card : ℝ)^2*(threshold N)^2*(10*(1+Real.log (N : ℝ))) ≤ envelope N at hScalar
  exact hBound.trans hScalar

theorem sampled_small_uniform (B : ℕ) (hB : 32 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ {ι : Type u837} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
        ‖DirichletPolynomialMeanValue.value
          (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f (τ r)‖ ≤ threshold N) →
      (∑ r ∈ R, ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
        (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f (τ r)‖^2) ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := sampled_rectangle_bound B hB
  obtain ⟨NE,hE⟩ := Filter.eventually_atTop.mp (envelope_tendsto.eventually (eventually_lt_nhds hε))
  refine ⟨max NB NE,by omega,?_⟩
  intro N hN f hf ι R τ T hT hTN hInside hsep hSmall
  exact (hBound N (by omega) f hf R τ T hT hTN hInside hsep hSmall).trans (hE N (by omega)).le
end PaperP1.FinalSmallPrimeSamples
