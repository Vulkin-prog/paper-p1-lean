module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.MixedFrequencyAmplification

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualMixedPrimeMean
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem continuous_mixed_bound (k : ℕ) (P Q B : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U M K : ℕ)
    (hL : 0 < L) (hLU : L ≤ U) (hM : 0 < M) (hMK : M ≤ K)
    (hBand : P ⊆ Icc L U) (hB : B ⊆ Icc M K) (f g b : ℕ → ℂ)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1)
    (T v w : ℝ) (hT : 0 < T) (hv : 0 < v) (hw : 0 ≤ w) :
    (∫ t in MixedFrequencyAmplification.mixedSet (DirichletPolynomialMeanValue.value P f)
      (DirichletPolynomialMeanValue.value Q g) T v w,
      ‖DirichletPolynomialMeanValue.value Q g t*DirichletPolynomialMeanValue.value B b t‖^2) ≤
      (w^2/v^(2*k))*(Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*((U^k*K : ℕ) : ℝ))*
        (((U^k*K : ℕ) : ℝ)/((L^k*M : ℕ) : ℝ)^2*AmplifiedPrimeProductMean.budget k P)) := by
  have hi := MixedFrequencyAmplification.mixedSet_bound k
    (DirichletPolynomialMeanValue.value P f) (DirichletPolynomialMeanValue.value Q g)
    (DirichletPolynomialMeanValue.value B b) (GaussianExponentialSums.polynomial_continuous _ _ _)
    (GaussianExponentialSums.polynomial_continuous _ _ _) (GaussianExponentialSums.polynomial_continuous _ _ _)
    T v w hT.le hv hw
  have hm := AmplifiedPrimeProductMean.continuous_mean_bound k P B hP hMass L U M K hL hLU hM hMK hBand hB f b hf hb T hT
  exact hi.trans (mul_le_mul_of_nonneg_left hm (by positivity))

theorem sampled_mixed_bound {ι : Type*} (k : ℕ) (P Q B : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U M K : ℕ)
    (hL : 0 < L) (hLU : L ≤ U) (hM : 0 < M) (hMK : M ≤ K)
    (hBand : P ⊆ Icc L U) (hB : B ⊆ Icc M K) (f g b : ℕ → ℂ)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T v w : ℝ) (hT : 0 < T) (hv : 0 < v) (hw : 0 ≤ w)
    (hregion : ∀ r ∈ R, τ r ∈ MixedFrequencyAmplification.mixedSet
      (DirichletPolynomialMeanValue.value P f) (DirichletPolynomialMeanValue.value Q g) T v w)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value Q g (τ r)*DirichletPolynomialMeanValue.value B b (τ r)‖^2) ≤
      (w^2/v^(2*k))*(Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*((U^k*K : ℕ) : ℝ))*
        (2+(Real.log ((U^k*K : ℕ) : ℝ)-Real.log ((L^k*M : ℕ) : ℝ))^2)*
        (((U^k*K : ℕ) : ℝ)/((L^k*M : ℕ) : ℝ)^2*AmplifiedPrimeProductMean.budget k P)) := by
  have hi := sum_le_sum (s := R) (fun r hr ↦ MixedFrequencyAmplification.pointwise_bound k
    (DirichletPolynomialMeanValue.value P f (τ r)) (DirichletPolynomialMeanValue.value Q g (τ r))
    (DirichletPolynomialMeanValue.value B b (τ r)) v w hv hw (hregion r hr).2.1 (hregion r hr).2.2)
  rw [← mul_sum] at hi
  have hm := AmplifiedPrimeProductMean.sampled_mean_bound k P B hP hMass L U M K hL hLU hM hMK hBand hB f b hf hb R τ T hT
    (fun r hr ↦ ⟨(hregion r hr).1.1.le,(hregion r hr).1.2⟩) hsep
  exact hi.trans (mul_le_mul_of_nonneg_left hm (by positivity))
end PaperP1.ActualMixedPrimeMean
