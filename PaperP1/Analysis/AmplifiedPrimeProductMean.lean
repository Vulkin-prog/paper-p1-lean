module

public import PaperP1.Analysis.DirichletProductMeanValue
public import PaperP1.Analysis.PrimePowerPolynomial
public import PaperP1.Analysis.PrimeProductLcmKernel

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.AmplifiedPrimeProductMean
open Finset PaperP1 MeasureTheory
open scoped Classical

def budget (k : ℕ) (P : Finset ℕ) : ℝ :=
  (k.factorial : ℝ)^2*(16 : ℝ)^k*((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k

theorem budget_nonneg (k : ℕ) (P : Finset ℕ) : 0 ≤ budget k P := by
  unfold budget
  have hh : (0 : ℝ) ≤ ∑ p ∈ P, 1/(p : ℝ) := sum_nonneg (fun p hp ↦ by positivity)
  positivity

theorem continuous_mean_bound (k : ℕ) (P B : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U M K : ℕ)
    (hL : 0 < L) (hLU : L ≤ U) (hM : 0 < M) (hMK : M ≤ K)
    (hBand : P ⊆ Icc L U) (hB : B ⊆ Icc M K) (f b : ℕ → ℂ)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖(DirichletPolynomialMeanValue.value P f t)^k*DirichletPolynomialMeanValue.value B b t‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*((U^k*K : ℕ) : ℝ))*
        (((U^k*K : ℕ) : ℝ)/((L^k*M : ℕ) : ℝ)^2*budget k P) := by
  have hh := DirichletProductMeanValue.continuous_mean_bound (PrimePowerPolynomial.layer k P) B
    (L^k) (U^k) M K (pow_pos hL k) (Nat.pow_le_pow_left hLU k) hM hMK
    (PrimePowerPolynomial.layer_bounds k P L U hBand) hB
    (PrimePowerPolynomial.coefficient k P f) b (fun _ ↦ (k.factorial : ℝ))
    (fun n _hn ↦ PrimePowerPolynomial.coefficient_norm_bound k P hP f hf n) hb T hT
  have hker : WeightedDivisorSquare.kernel (PrimePowerPolynomial.layer k P) id (fun _ ↦ (k.factorial : ℝ)) ≤ budget k P :=
    PrimeProductLcmKernel.factorial_weight_kernel_bound k P hP hMass
  simp_rw [PrimePowerPolynomial.power_identity k P (fun p hp ↦ (hP p hp).pos) f]
  exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hker (by positivity)) (by positivity))

theorem sampled_mean_bound {ι : Type*} (k : ℕ) (P B : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) (L U M K : ℕ)
    (hL : 0 < L) (hLU : L ≤ U) (hM : 0 < M) (hMK : M ≤ K)
    (hBand : P ⊆ Icc L U) (hB : B ⊆ Icc M K) (f b : ℕ → ℂ)
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖(DirichletPolynomialMeanValue.value P f (τ r))^k*DirichletPolynomialMeanValue.value B b (τ r)‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*((U^k*K : ℕ) : ℝ))*
        (2+(Real.log ((U^k*K : ℕ) : ℝ)-Real.log ((L^k*M : ℕ) : ℝ))^2)*
        (((U^k*K : ℕ) : ℝ)/((L^k*M : ℕ) : ℝ)^2*budget k P) := by
  have hh := DirichletProductMeanValue.sampled_mean_bound (PrimePowerPolynomial.layer k P) B
    (L^k) (U^k) M K (pow_pos hL k) (Nat.pow_le_pow_left hLU k) hM hMK
    (PrimePowerPolynomial.layer_bounds k P L U hBand) hB
    (PrimePowerPolynomial.coefficient k P f) b (fun _ ↦ (k.factorial : ℝ))
    (fun n _hn ↦ PrimePowerPolynomial.coefficient_norm_bound k P hP f hf n) hb R τ T hT htau hsep
  have hker : WeightedDivisorSquare.kernel (PrimePowerPolynomial.layer k P) id (fun _ ↦ (k.factorial : ℝ)) ≤ budget k P :=
    PrimeProductLcmKernel.factorial_weight_kernel_bound k P hP hMass
  simp_rw [PrimePowerPolynomial.power_identity k P (fun p hp ↦ (hP p hp).pos) f]
  exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hker (by positivity)) (by positivity))
end PaperP1.AmplifiedPrimeProductMean
