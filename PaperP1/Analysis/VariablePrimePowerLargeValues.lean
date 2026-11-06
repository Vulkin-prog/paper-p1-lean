module

public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.BoundedAmplificationFactor
public import PaperP1.Analysis.RoundedAmplificationGeometry
public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.PrimePowerLargeValues
public import PaperP1.Analysis.VariableAmplificationSpan

set_option autoImplicit false
@[expose] public noncomputable section
universe u827
namespace PaperP1.VariablePrimePowerLargeValues
open Finset PaperP1
open scoped Classical

theorem sampled_moment_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hBand : P ⊆ Icc L U)
    (r : ℝ) (hr : 0 ≤ r)
    (hspan : ((U^k : ℕ) : ℝ) ≤ Real.exp (3*r)*((L^k : ℕ) : ℝ))
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    {ι : Type u827} (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (hTL : T ≤ ((L^k : ℕ) : ℝ))
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ r)‖^(2*k)) ≤
      VariableAmplificationSpan.constant*Real.exp (6*r)*(2+9*r^2)*AmplifiedPrimeProductMean.budget k P := by
  have hB : ({1} : Finset ℕ) ⊆ Icc 1 1 := by simp
  have hb : ∀ m ∈ ({1} : Finset ℕ), ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hm := AmplifiedPrimeProductMean.sampled_mean_bound k P {1} hP hMass L U 1 1 hL hLU
    (by norm_num) le_rfl hBand hB f (fun _ ↦ (1 : ℂ)) hf hb R τ T hT htau hsep
  simp only [PrimePowerLargeValues.value_singleton,mul_one,norm_pow,← pow_mul,Nat.mul_comm k 2] at hm
  have hLk : 0 < L^k := pow_pos hL k
  have hLp : (0 : ℝ) < ((L^k : ℕ) : ℝ) := by exact_mod_cast hLk
  have hLM : L^k ≤ U^k := Nat.pow_le_pow_left hLU k
  obtain ⟨hd0,hdr⟩ := VariableAmplificationSpan.bandwidth_bound (L^k) (U^k) hLk hLM r hspan
  have hBudget := AmplifiedPrimeProductMean.budget_nonneg k P
  have hOne : (1 : ℝ) ≤ ((L^k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L^k by omega)
  have hh := VariableAmplificationSpan.sampled_factor_bound ((L^k : ℕ) : ℝ) ((U^k : ℕ) : ℝ)
    T (AmplifiedPrimeProductMean.budget k P) (Real.log ((U^k : ℕ) : ℝ)-Real.log ((L^k : ℕ) : ℝ))
    r hOne (Nat.cast_nonneg _) hspan hT.le hTL hBudget hd0 hdr hr
  exact hm.trans hh

theorem sampled_large_values_card (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hBand : P ⊆ Icc L U)
    (r : ℝ) (hr : 0 ≤ r)
    (hspan : ((U^k : ℕ) : ℝ) ≤ Real.exp (3*r)*((L^k : ℕ) : ℝ))
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    {ι : Type u827} (R : Finset ι) (τ : ι → ℝ) (T V : ℝ) (hT : 0 < T) (hV : 0 < V)
    (hTL : T ≤ ((L^k : ℕ) : ℝ))
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, V ≤ ‖DirichletPolynomialMeanValue.value P f (τ r)‖) :
    (R.card : ℝ) ≤ VariableAmplificationSpan.constant*Real.exp (6*r)*(2+9*r^2)*AmplifiedPrimeProductMean.budget k P/V^(2*k) := by
  apply (le_div_iff₀ (pow_pos hV (2*k))).mpr
  have hsum : (R.card : ℝ)*V^(2*k) ≤ ∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ r)‖^(2*k) := by
    simpa only [sum_const,nsmul_eq_mul] using
      sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hLarge r hr) (2*k))
  exact hsum.trans (sampled_moment_bound k P hP hMass L U hL hLU hBand r hr hspan f hf R τ T hT hTL htau hsep)
end PaperP1.VariablePrimePowerLargeValues
