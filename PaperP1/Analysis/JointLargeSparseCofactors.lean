module

public import PaperP1.Analysis.JointLargeFrequencyReduction
public import PaperP1.Analysis.ExpandedCofactorSparseMean
public import PaperP1.Analysis.SecondBadFrequencyCardinality

set_option autoImplicit false
@[expose] public noncomputable section
universe u834
namespace PaperP1.JointLargeSparseCofactors
open Finset PaperP1
open scoped Classical

theorem frequency_card_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u834} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (R.card : ℝ) ≤ (N : ℝ)^(1/18 : ℝ) := by
  obtain ⟨N₀,hN₀,hCard⟩ := SecondBadFrequencyCardinality.all_blocks_uniform.{u834}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf ι R τ T hT hTN hInside hsep
  have htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T := by
    intro r hr
    have hh := ((JointLargeFrequencyReduction.largeRegion_iff N f T (τ r)).mp (hInside r hr)).1
    exact ⟨hh.1.le,hh.2⟩
  apply hCard N hN f hf R τ T hT hTN htau hsep
  intro r hr
  obtain ⟨j,hj,hLarge⟩ := ((JointLargeFrequencyReduction.largeRegion_iff N f T (τ r)).mp (hInside r hr)).2.2
  exact ⟨j,hj,hLarge.le⟩

theorem cofactor_mean_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ p ∈ TwoPrimeBandPopulation.second N, ‖f p‖ ≤ 1) →
      ∀ {ι : Type u834} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (N : ℝ) →
      (∀ r ∈ R, τ r ∈ JointLargeFrequencyReduction.largeRegion N f T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ H j : ℕ, NarrowPrimeBands.anchor H j ≤ (N : ℝ)^(1/16 : ℝ) →
      ∀ P Q : Finset ℕ, ∀ g : ℕ → ℂ,
      (∀ n ∈ NarrowRamareRectangle.cofactorSet N H j, ‖g n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j)
        (NarrowRamareRectangle.coefficient P Q g) (τ r)‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
  obtain ⟨NC,hNC,hCard⟩ := frequency_card_uniform.{u834}
  obtain ⟨NS,hNS,hSample⟩ := ExpandedCofactorSparseMean.sparse_mean_uniform.{u834}
  refine ⟨max NC NS,by omega,?_⟩
  intro N hN f hf ι R τ T hT hTN hInside hsep H j hAnchor P Q g hg
  have hCardR := hCard N (by omega) f hf R τ T (by linarith only [hT]) hTN hInside hsep
  have htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T := by
    intro r hr
    have hh := ((JointLargeFrequencyReduction.largeRegion_iff N f T (τ r)).mp (hInside r hr)).1
    exact ⟨hh.1.le,hh.2⟩
  exact hSample N (by omega) H j hAnchor R τ T hT hTN hCardR htau hsep P Q g hg
end PaperP1.JointLargeSparseCofactors
