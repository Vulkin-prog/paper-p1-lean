module

public import PaperP1.Analysis.PrimeHalaszLogarithmicSamples
public import PaperP1.Analysis.DyadicPrimeCoefficientEnergy


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeDirichletLogarithmicSamples
open Finset Filter PaperP1
open scoped Classical

def constant (B : ℝ) : ℝ := PrimeHalaszLogarithmicSamples.constant B*DyadicPrimeCoefficientEnergy.constant

theorem constant_pos (B : ℝ) : 0 < constant B :=
  mul_pos (PrimeHalaszLogarithmicSamples.constant_pos B) DyadicPrimeCoefficientEnergy.constant_pos

theorem uniform_bound {ι : Type*} (B C : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ R : Finset ι, ∀ τ : ι → ℝ,
      (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
      (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
      (R.card : ℝ) ≤ (Real.log A)^C →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) →
      ∀ f : ℕ → ℂ, (∀ p ∈ P, ‖f p‖ ≤ 1) →
      (∑ i ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ i)‖^2) ≤ constant B/(Real.log A)^2 := by
  obtain ⟨A₀,hA₀,hAnalysis⟩ := PrimeHalaszLogarithmicSamples.uniform_analysis (ι := ι) B C hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA R τ hSep hHeight hCard P hP f hf
  have hA8 : 8 ≤ A := hA₀.trans hA
  have hA2 : 2 ≤ A := by linarith only [hA8]
  have hAP : 0 < A := by linarith only [hA8]
  have hLog : 0 < Real.log A := Real.log_pos (by linarith only [hA8])
  have hK := PrimeHalaszLogarithmicSamples.constant_pos B
  have hActual := hAnalysis A hA R τ hSep hHeight hCard P hP (fun p ↦ f p/(p : ℂ))
  change (∑ i ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ i)‖^2) ≤
    (PrimeHalaszLogarithmicSamples.constant B*A/Real.log A)*(∑ p ∈ P, ‖f p/(p : ℂ)‖^2) at hActual
  calc
    _ ≤ _ := hActual
    _ ≤ (PrimeHalaszLogarithmicSamples.constant B*A/Real.log A)*
        (DyadicPrimeCoefficientEnergy.constant/(A*Real.log A)) :=
      mul_le_mul_of_nonneg_left (DyadicPrimeCoefficientEnergy.coefficient_energy A hA2 P hP f hf) (by positivity)
    _ = _ := by unfold constant; field_simp [hAP.ne',hLog.ne']
end PaperP1.PrimeDirichletLogarithmicSamples
