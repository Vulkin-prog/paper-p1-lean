module

public import PaperP1.Analysis.MixedFrequencyAmplification
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.ActualNarrowAmplifiedMean
public import PaperP1.Analysis.BoundedAmplificationFactor

set_option autoImplicit false
@[expose] public noncomputable section
universe u800
namespace PaperP1.ActualNarrowMixedMean
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem estimates (X H j l k : ℕ) (hX : 0 < X) (hH : 4 ≤ H) (hk : k ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (P D Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hfP : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hfB : ∀ n ∈ NarrowRamareRectangle.cofactorSet X H l, ‖f n‖ ≤ 1)
    (T v w : ℝ) (hT : 0 < T) (hv : 0 < v) (hw : 0 ≤ w) :
    (∫ t in MixedFrequencyAmplification.mixedSet
      (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f)
      (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f) T v w,
      ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f t*
        DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l)
          (NarrowRamareRectangle.coefficient D Q f) t‖^2) ≤
      (w^2/v^(2*k))*(BoundedAmplificationFactor.constant*
        (T/((⌈NarrowPrimeBands.anchor H j⌉₊^k*⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ)+1)*
        AmplifiedPrimeProductMean.budget k (NarrowPrimeBands.band H P j)) ∧
    ∀ {ι : Type u800} (R : Finset ι) (τ : ι → ℝ),
      (∀ r ∈ R, τ r ∈ MixedFrequencyAmplification.mixedSet
        (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f)
        (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f) T v w) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f (τ r)*
        DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l)
          (NarrowRamareRectangle.coefficient D Q f) (τ r)‖^2) ≤
        (w^2/v^(2*k))*(18*BoundedAmplificationFactor.constant*
          ((T+1)/((⌈NarrowPrimeBands.anchor H j⌉₊^k*⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ)+1)*
          AmplifiedPrimeProductMean.budget k (NarrowPrimeBands.band H P j)) := by
  have hm := ActualNarrowAmplifiedMean.estimates.{u800} X H j l k hX hH hk hj P D Q hP f hfP hfB T hT
  have hc : 0 ≤ w^2/v^(2*k) := by positivity
  have hi := MixedFrequencyAmplification.mixedSet_bound k
    (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f)
    (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f)
    (DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l) (NarrowRamareRectangle.coefficient D Q f))
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (GaussianExponentialSums.polynomial_continuous _ _ _) T v w hT.le hv hw
  constructor
  · exact hi.trans (mul_le_mul_of_nonneg_left hm.1 hc)
  · intro ι R τ hregion hsep
    have hs := sum_le_sum (s := R) (fun r hr ↦ MixedFrequencyAmplification.pointwise_bound k
      (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r))
      (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H D l) f (τ r))
      (DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l)
        (NarrowRamareRectangle.coefficient D Q f) (τ r)) v w hv hw (hregion r hr).2.1 (hregion r hr).2.2)
    rw [← mul_sum] at hs
    have hb := hm.2 R τ (fun r hr ↦ ⟨(hregion r hr).1.1.le,(hregion r hr).1.2⟩) hsep
    exact hs.trans (mul_le_mul_of_nonneg_left hb hc)
end PaperP1.ActualNarrowMixedMean
