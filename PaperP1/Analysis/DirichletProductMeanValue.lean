module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.DivisorMajorantMeanValue
public import PaperP1.Analysis.FiniteDirichletConvolution
public import PaperP1.Analysis.WeightedDivisorSquare

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DirichletProductMeanValue
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem continuous_mean_bound (A B : Finset ℕ) (L₁ U₁ L₂ U₂ : ℕ)
    (hL₁ : 0 < L₁) (hU₁ : L₁ ≤ U₁) (hL₂ : 0 < L₂) (hU₂ : L₂ ≤ U₂)
    (hA : A ⊆ Icc L₁ U₁) (hB : B ⊆ Icc L₂ U₂) (a b : ℕ → ℂ) (w : ℕ → ℝ)
    (ha : ∀ d ∈ A, ‖a d‖ ≤ w d) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value A a t*DirichletPolynomialMeanValue.value B b t‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*((U₁*U₂ : ℕ) : ℝ))*
        (((U₁*U₂ : ℕ) : ℝ)/((L₁*L₂ : ℕ) : ℝ)^2*WeightedDivisorSquare.kernel A id w) := by
  have hpA : ∀ d ∈ A, 0 < d := fun d hd ↦ hL₁.trans_le (mem_Icc.mp (hA hd)).1
  have hpB : ∀ m ∈ B, 0 < m := fun m hm ↦ hL₂.trans_le (mem_Icc.mp (hB hm)).1
  have hw : ∀ d ∈ A, 0 ≤ w d := fun d hd ↦ (norm_nonneg _).trans (ha d hd)
  simp_rw [FiniteDirichletConvolution.product_identity A B hpA hpB a b]
  exact DivisorMajorantMeanValue.mean_value_bound A id w hpA hw (L₁*L₂) (U₁*U₂)
    (by positivity) (Nat.mul_pos (by omega) (by omega)) (FiniteDirichletConvolution.support A B)
    (FiniteDirichletConvolution.support_bounds A B L₁ U₁ L₂ U₂ hA hB)
    (FiniteDirichletConvolution.coefficient A B a b)
    (fun n _hn ↦ FiniteDirichletConvolution.coefficient_norm_bound A B a b w ha hb n) T hT

theorem sampled_mean_bound {ι : Type*} (A B : Finset ℕ) (L₁ U₁ L₂ U₂ : ℕ)
    (hL₁ : 0 < L₁) (hU₁ : L₁ ≤ U₁) (hL₂ : 0 < L₂) (hU₂ : L₂ ≤ U₂)
    (hA : A ⊆ Icc L₁ U₁) (hB : B ⊆ Icc L₂ U₂) (a b : ℕ → ℂ) (w : ℕ → ℝ)
    (ha : ∀ d ∈ A, ‖a d‖ ≤ w d) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1)
    (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value A a (τ r)*DirichletPolynomialMeanValue.value B b (τ r)‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*((U₁*U₂ : ℕ) : ℝ))*
        (2+(Real.log ((U₁*U₂ : ℕ) : ℝ)-Real.log ((L₁*L₂ : ℕ) : ℝ))^2)*
        (((U₁*U₂ : ℕ) : ℝ)/((L₁*L₂ : ℕ) : ℝ)^2*WeightedDivisorSquare.kernel A id w) := by
  have hpA : ∀ d ∈ A, 0 < d := fun d hd ↦ hL₁.trans_le (mem_Icc.mp (hA hd)).1
  have hpB : ∀ m ∈ B, 0 < m := fun m hm ↦ hL₂.trans_le (mem_Icc.mp (hB hm)).1
  have hw : ∀ d ∈ A, 0 ≤ w d := fun d hd ↦ (norm_nonneg _).trans (ha d hd)
  simp_rw [FiniteDirichletConvolution.product_identity A B hpA hpB a b]
  exact DivisorMajorantMeanValue.sampled_mean_value_bound A id w hpA hw (L₁*L₂) (U₁*U₂)
    (by positivity) (Nat.mul_pos (by omega) (by omega)) (FiniteDirichletConvolution.support A B)
    (FiniteDirichletConvolution.support_bounds A B L₁ U₁ L₂ U₂ hA hB)
    (FiniteDirichletConvolution.coefficient A B a b)
    (fun n _hn ↦ FiniteDirichletConvolution.coefficient_norm_bound A B a b w ha hb n) R τ T hT htau hsep
end PaperP1.DirichletProductMeanValue
