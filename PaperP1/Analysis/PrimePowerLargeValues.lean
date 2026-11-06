module

public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.BoundedAmplificationFactor
public import PaperP1.Analysis.RoundedAmplificationGeometry
public import PaperP1.Analysis.NarrowBandReciprocalMass

set_option autoImplicit false
@[expose] public noncomputable section
universe u822
namespace PaperP1.PrimePowerLargeValues
open Finset PaperP1
open scoped Classical

theorem value_singleton (t : ℝ) :
    DirichletPolynomialMeanValue.value {1} (fun _ ↦ (1 : ℂ)) t=1 := by
  simp [DirichletPolynomialMeanValue.value,GaussianExponentialSums.polynomial,
    LogarithmicPhase.phase_zero]

theorem sampled_moment_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hBand : P ⊆ Icc L U)
    (hspan : ((U^k : ℕ) : ℝ) ≤ BoundedAmplificationFactor.span*((L^k : ℕ) : ℝ))
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    {ι : Type u822} (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (hTL : T ≤ ((L^k : ℕ) : ℝ))
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ r)‖^(2*k)) ≤
      54*BoundedAmplificationFactor.constant*AmplifiedPrimeProductMean.budget k P := by
  have hB : ({1} : Finset ℕ) ⊆ Icc 1 1 := by simp
  have hb : ∀ m ∈ ({1} : Finset ℕ), ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hm := AmplifiedPrimeProductMean.sampled_mean_bound k P {1} hP hMass L U 1 1 hL hLU
    (by norm_num) le_rfl hBand hB f (fun _ ↦ (1 : ℂ)) hf hb R τ T hT htau hsep
  simp only [value_singleton,mul_one,norm_pow,← pow_mul,Nat.mul_comm k 2] at hm
  have hLk : 0 < L^k := pow_pos hL k
  have hLp : (0 : ℝ) < ((L^k : ℕ) : ℝ) := by exact_mod_cast hLk
  have hLM : L^k ≤ U^k := Nat.pow_le_pow_left hLU k
  obtain ⟨hd0,hd4⟩ := RoundedAmplificationGeometry.bandwidth_bound (L^k) (U^k) hLk hLM hspan
  have hBudget := AmplifiedPrimeProductMean.budget_nonneg k P
  have hh := BoundedAmplificationFactor.sampled_factor_bound ((L^k : ℕ) : ℝ) ((U^k : ℕ) : ℝ)
    T (AmplifiedPrimeProductMean.budget k P) (Real.log ((U^k : ℕ) : ℝ)-Real.log ((L^k : ℕ) : ℝ))
    hLp (Nat.cast_nonneg _) hspan hT.le hBudget hd0 hd4
  have hOne : (1 : ℝ) ≤ ((L^k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L^k by omega)
  have hRatio : (T+1)/((L^k : ℕ) : ℝ)+1 ≤ 3 := by
    have hhq : (T+1)/((L^k : ℕ) : ℝ) ≤ 2 := (div_le_iff₀ hLp).mpr (by linarith only [hTL,hOne])
    linarith only [hhq]
  have hc := BoundedAmplificationFactor.constant_pos
  calc
    _ ≤ _ := hm.trans hh
    _ ≤ _ := by nlinarith only [mul_nonneg hc.le hBudget,hRatio]

theorem sampled_large_values_card (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U)
    (hBand : P ⊆ Icc L U)
    (hspan : ((U^k : ℕ) : ℝ) ≤ BoundedAmplificationFactor.span*((L^k : ℕ) : ℝ))
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    {ι : Type u822} (R : Finset ι) (τ : ι → ℝ) (T V : ℝ) (hT : 0 < T) (hV : 0 < V)
    (hTL : T ≤ ((L^k : ℕ) : ℝ))
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hLarge : ∀ r ∈ R, V ≤ ‖DirichletPolynomialMeanValue.value P f (τ r)‖) :
    (R.card : ℝ) ≤ 54*BoundedAmplificationFactor.constant*AmplifiedPrimeProductMean.budget k P/V^(2*k) := by
  apply (le_div_iff₀ (pow_pos hV (2*k))).mpr
  have hsum : (R.card : ℝ)*V^(2*k) ≤ ∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P f (τ r)‖^(2*k) := by
    simpa only [sum_const,nsmul_eq_mul] using
      sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ hV.le (hLarge r hr) (2*k))
  exact hsum.trans (sampled_moment_bound k P hP hMass L U hL hLU hBand hspan f hf R τ T hT hTL htau hsep)
end PaperP1.PrimePowerLargeValues
