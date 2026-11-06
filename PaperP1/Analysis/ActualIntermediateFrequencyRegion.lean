module

public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.ActualMixedPairDecay
public import PaperP1.Analysis.FiniteFrequencyCover

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualIntermediateFrequencyRegion
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

def region (N : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc (-T) T ∧
    (∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      FirstBandSmallRegion.threshold N <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f t‖) ∧
    (∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f t‖ ≤
        (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/40 : ℝ))}

theorem region_measurable (N : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (region N f T) := by
  have hb : IsOpen {t : ℝ | ∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      FirstBandSmallRegion.threshold N <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f t‖} := by
    simp only [Set.ofPred_exists]
    apply isOpen_iUnion
    intro j
    by_cases hj : j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N)
    · simpa only [hj,true_and,DirichletPolynomialMeanValue.value] using
        isOpen_lt continuous_const (GaussianExponentialSums.polynomial_continuous _ _ _ |>.norm)
    · simp [hj]
  have hg : IsClosed {t : ℝ | ∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f t‖ ≤
        (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/40 : ℝ)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro l
    apply isClosed_iInter
    intro hl
    exact isClosed_le (GaussianExponentialSums.polynomial_continuous _ _ _ |>.norm) continuous_const
  exact measurableSet_Ioc.inter (hb.measurableSet.inter hg.measurableSet)

theorem cover_by_pairs (N : ℕ) (f : ℕ → ℂ) (T : ℝ) (l : ℕ)
    (hl : l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N)) :
    region N f T ⊆ ⋃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      ActualMixedPairDecay.region N j l f T := by
  intro t ht
  obtain ⟨htime,⟨j,hj,hbig⟩,hsmall⟩ := ht
  exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,⟨htime,hbig.le,hsmall l hl⟩⟩⟩

theorem rectangle_bound : ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
    (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
    (∫ t in region N f T, ‖NarrowRamareRectangle.rectangle N (GrowingFirstGoodRegion.width N)
      (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤
    ((NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N)).card : ℝ)*
      ((NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N)).card : ℝ)*
      (∑ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
        2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/100 : ℝ)) := by
  obtain ⟨N₀,hN₀,hpair⟩ := ActualMixedPairDecay.estimates.{0}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf T hT hTN
  let J := NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N)
  let K := NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N)
  have hh := FiniteFrequencyCover.finite_sum_cover_bound J K (fun l ↦ ActualMixedPairDecay.term N l f)
    (fun l hl ↦ ActualMixedPairDecay.term_continuous N l f) (region N f T) T
    (fun j l ↦ ActualMixedPairDecay.region N j l f T)
    (fun l ↦ 2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/100 : ℝ))
    (region_measurable N f T) (fun _t ht ↦ ht.1)
    (fun j hj l hl ↦ ActualMixedPairDecay.region_measurable N j l f T)
    (fun j hj l hl _t ht ↦ ht.1) (fun l hl ↦ cover_by_pairs N f T l hl)
    (fun j hj l hl ↦ (hpair N hN j hj l hl f hf T hT hTN).1)
  simp_rw [← ActualMixedPairDecay.sum_terms N f]
  exact hh
end PaperP1.ActualIntermediateFrequencyRegion
