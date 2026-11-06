module

public import PaperP1.Analysis.FirstGoodFullPolynomial
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.GrowingFirstGoodRegion

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GrowingGoodFullPolynomial
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

theorem first_good_part_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N),
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨H₀,hH₀,N₁,hN₁,happrox⟩ := TwoBandRectangleApproximation.both_rectangles_small_uniform (ε/4) (by positivity)
  obtain ⟨N₂,hN₂,hgood⟩ := GrowingFirstGoodRegion.rectangle_small_uniform (ε/4) (by positivity)
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  obtain ⟨NH,hH⟩ := eventually_atTop.mp (GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop H₀))
  obtain ⟨NG,hG⟩ := eventually_atTop.mp GrowingFirstGoodRegion.width_geometry
  refine ⟨max N₁ (max N₂ (max NU (max NH NG))),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  have hlog1 : 1 ≤ Real.log (N : ℝ) := hU N (by omega)
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  have hTX : T ≤ N := hTN.trans ((div_le_iff₀ hlog).mpr (by
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [hlog1,hNN]))
  have hbf : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (by have := (mem_Ico.mp hn).1; omega)
  have hbi : ∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (by have := (mem_Icc.mp hn).1; omega)
  have hw := hG N (by omega)
  have hr := (happrox (GrowingFirstGoodRegion.width N) (hH N (by omega)) N (by omega) f hf hbf T hT hTX).1
  have hg := hgood N (by omega) (GrowingFirstGoodRegion.width N) (by omega) hw.2.1
    (TwoPrimeBandPopulation.second N) f hbi T hT hTN
  have hh := FirstGoodFullPolynomial.restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _) _
    (SmallPrimeRegion.goodSet_measurable (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N))
    T hT.le (fun _t ht ↦ ht.1)
  linarith only [hh,hr,hg]
end PaperP1.GrowingGoodFullPolynomial
