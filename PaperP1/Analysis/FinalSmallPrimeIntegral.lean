module

public import PaperP1.Analysis.FinalSmallPrimeSamples
public import PaperP1.Analysis.FinalRectangleApproximation
public import PaperP1.Analysis.FirstGoodFullPolynomial
public import PaperP1.Analysis.SeparatedIntegralBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalSmallPrimeIntegral
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def region (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  JointLargeFrequencyReduction.largeRegion N f T ∩
    SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) f T
      (FinalSmallPrimeSamples.threshold N)

theorem region_measurable (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (region B N f T) :=
  (JointLargeFrequencyReduction.largeRegion_measurable N f T).inter
    (SmallPrimeRegion.goodSet_measurable _ _ f T _)

theorem rectangle_bound (B : ℕ) (hB : 32 ≤ B) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in region B N f T, ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
        (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤
        4*FinalSmallPrimeSamples.envelope N := by
  obtain ⟨N₀,hN₀,hSample⟩ := FinalSmallPrimeSamples.sampled_rectangle_bound.{0} B hB
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf T hT hTN
  have hC : Continuous (fun t ↦ ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
      (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f t‖^2) :=
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _).norm.pow 2
  apply SeparatedIntegralBound.bound (region B N f T) T _ hC (fun t ↦ sq_nonneg _)
    (region_measurable B N f T) (fun t ht ↦
      ((JointLargeFrequencyReduction.largeRegion_iff N f T t).mp ht.1).1)
    (FinalSmallPrimeSamples.envelope N)
  intro R τ hInside hsep
  exact hSample N hN f hf R τ T hT hTN (fun r hr ↦ (hInside r hr).1) hsep
    (fun r hr j hj ↦ (hInside r hr).2.2 j hj)

theorem rectangle_small_uniform (B : ℕ) (hB : 32 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in region B N f T, ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
        (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := rectangle_bound B hB
  have hLim : Tendsto (fun N ↦ 4*FinalSmallPrimeSamples.envelope N) atTop (nhds 0) := by
    simpa only [mul_zero] using FinalSmallPrimeSamples.envelope_tendsto.const_mul 4
  obtain ⟨NE,hE⟩ := eventually_atTop.mp (hLim.eventually (eventually_lt_nhds hε))
  refine ⟨max NB NE,by omega,?_⟩
  intro N hN f hf T hT hTN
  exact (hBound N (by omega) f hf T hT hTN).trans (hE N (by omega)).le

theorem full_small_uniform (B : ℕ) (hB : 32 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in region B N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨NR,hNR,hRect⟩ := rectangle_small_uniform B hB (ε/4) (by positivity)
  obtain ⟨H₀,hH₀,NA,hNA,hApprox⟩ := FinalRectangleApproximation.rectangle_small_uniform B hB (ε/4) (by positivity)
  obtain ⟨NH,hH⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop H₀))
  refine ⟨max NR (max NA NH),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  have hTp : 0 < T := by linarith only [hT]
  have hWide : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 :=
    fun n hn ↦ hb n (hNp.trans_le (mem_Ico.mp hn).1)
  have ha := hApprox (GrowingFirstGoodRegion.width N) (hH N (by omega)) N (by omega) f hf hWide T hTp hTN
  have hr := hRect N (by omega) f hb T hT hTN
  have hh := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
      (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _)
    (region B N f T) (region_measurable B N f T) T hTp.le
    (fun t ht ↦ ((JointLargeFrequencyReduction.largeRegion_iff N f T t).mp ht.1).1)
  linarith only [hh,ha,hr]
end PaperP1.FinalSmallPrimeIntegral
