module

public import PaperP1.Analysis.SmallPrimeRegion
public import PaperP1.Analysis.SeparatedIntegralBound
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.FixedPowerLargeRectangle


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerLargeIntegral
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def region (a b : ℝ) (H N : ℕ) (f : ℕ → ℂ) (T T₀ : ℝ) : Set ℝ :=
  (Set.Ioc (-T) T \ SmallPrimeRegion.goodSet H (FixedPowerPrimeBand.primes a b N) f T
    (1/(Real.log (N : ℝ))^100)) ∩ {t : ℝ | T₀ ≤ |t|}

theorem region_measurable (a b : ℝ) (H N : ℕ) (f : ℕ → ℂ) (T T₀ : ℝ) :
    MeasurableSet (region a b H N f T T₀) :=
  (measurableSet_Ioc.diff (SmallPrimeRegion.goodSet_measurable _ _ f T _)).inter
    (isClosed_le continuous_const continuous_abs).measurableSet

theorem region_iff (a b : ℝ) (H N : ℕ) (f : ℕ → ℂ) (T T₀ t : ℝ) :
    t ∈ region a b H N f T T₀ ↔ t ∈ Set.Ioc (-T) T ∧ T₀ ≤ |t| ∧
      ∃ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        1/(Real.log (N : ℝ))^100 <
          ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f t‖ := by
  constructor
  · rintro ⟨⟨ht,hNot⟩,hAway⟩
    have hNotAll : ¬∀ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j) f t‖ ≤
          1/(Real.log (N : ℝ))^100 := fun hh ↦ hNot ⟨ht,hh⟩
    push Not at hNotAll
    exact ⟨ht,hAway,hNotAll⟩
  · rintro ⟨ht,hAway,⟨j,hj,hBig⟩⟩
    refine ⟨⟨ht,?_⟩,hAway⟩
    intro hGood
    exact (not_lt_of_ge (hGood.2 j hj)) hBig

theorem uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b ≤ 1/16)
    (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      (∫ t in region a b H N (fun n ↦ (f n : ℂ)) T T₀,
        ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨T₀,hT₀,N₀,hN₀,hSample⟩ := FixedPowerLargeRectangle.uniform_bound (ι := ℕ) a b ha hb H hH hOrder (ε/4) (by positivity)
  refine ⟨T₀,hT₀,N₀,hN₀,?_⟩
  intro N hN Q hQ f hf T hT hTN
  have hContinuous : Continuous (fun t ↦
      ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q (fun n ↦ (f n : ℂ)) t‖^2) :=
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _).norm.pow 2
  calc
    _ ≤ 4*(ε/4) := by
      apply SeparatedIntegralBound.bound _ T _ hContinuous (fun _ ↦ sq_nonneg _)
        (region_measurable a b H N (fun n ↦ (f n : ℂ)) T T₀) (fun _ ht ↦ ht.1.1) (ε/4)
      intro R τ hInside hsep
      apply hSample N hN Q hQ f hf R τ T hT hTN
      · intro r hr
        have hh := ((region_iff a b H N (fun n ↦ (f n : ℂ)) T T₀ (τ r)).mp (hInside r hr)).1
        exact ⟨hh.1.le,hh.2⟩
      · intro r hr
        exact ((region_iff a b H N (fun n ↦ (f n : ℂ)) T T₀ (τ r)).mp (hInside r hr)).2.1
      · exact hsep
      · intro r hr
        obtain ⟨j,hj,hBig⟩ := ((region_iff a b H N (fun n ↦ (f n : ℂ)) T T₀ (τ r)).mp (hInside r hr)).2.2
        exact ⟨j,hj,hBig.le⟩
    _ = ε := by ring
end PaperP1.FixedPowerLargeIntegral
