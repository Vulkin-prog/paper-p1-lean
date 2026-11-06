module

public import PaperP1.Analysis.SmallPrimeRegion
public import PaperP1.Analysis.SeparatedIntegralBound
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.FixedPowerSmallSamples


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerSmallIntegral
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def region (a b : ℝ) (H N : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  JointLargeFrequencyReduction.largeRegion N f T ∩
    SmallPrimeRegion.goodSet H (FixedPowerPrimeBand.primes a b N) f T (1/(Real.log (N : ℝ))^100)

theorem region_measurable (a b : ℝ) (H N : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (region a b H N f T) :=
  (JointLargeFrequencyReduction.largeRegion_measurable N f T).inter
    (SmallPrimeRegion.goodSet_measurable _ _ f T _)

theorem uniform_bound (a b : ℝ) (hb : b ≤ 1/16) (H : ℕ) (hH : 4 ≤ H) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in region a b H N f T,
        ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q f t‖^2) ≤ ε := by
  obtain ⟨N₀,hN₀,hSample⟩ := FixedPowerSmallSamples.sampled_small_uniform (ι := ℕ) a b hb H hH (ε/4) (by positivity)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN Q f hf T hT hTN
  have hContinuous : Continuous (fun t ↦
      ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q f t‖^2) :=
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _).norm.pow 2
  calc
    _ ≤ 4*(ε/4) := by
      apply SeparatedIntegralBound.bound _ T _ hContinuous (fun _ ↦ sq_nonneg _)
        (region_measurable a b H N f T) (fun t ht ↦ ((JointLargeFrequencyReduction.largeRegion_iff N f T t).mp ht.1).1) (ε/4)
      intro R τ hInside hsep
      exact hSample N hN Q f hf R τ T hT hTN (fun r hr ↦ (hInside r hr).1) hsep
        (fun r hr j hj ↦ (hInside r hr).2.2 j hj)
    _ = ε := by ring
end PaperP1.FixedPowerSmallIntegral
