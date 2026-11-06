module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.PositiveSelbergGram
public import PaperP1.Analysis.PowerSelbergLevel
public import PaperP1.Analysis.SelbergLogarithmicBudget
public import PaperP1.Analysis.SelbergPrimeOperator
public import PaperP1.Analysis.UniformSelbergKernelEnvelope


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeHalaszLogarithmicSamples
open Finset Filter PaperP1
open scoped Classical

def constant (B : ℝ) : ℝ := Real.exp 2*SelbergLogarithmicBudget.constant B

theorem constant_pos (B : ℝ) : 0 < constant B :=
  mul_pos (Real.exp_pos 2) (SelbergLogarithmicBudget.constant_pos B)

theorem uniform_synthesis {ι : Type*} (B C : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ R : Finset ι, ∀ τ : ι → ℝ,
      (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
      (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
      (R.card : ℝ) ≤ (Real.log A)^C →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) → ∀ b : ι → ℂ,
      (∑ p ∈ P, ‖PositiveSelbergGram.polynomial R b τ p‖^2) ≤
        (constant B*A/Real.log A)*(∑ i ∈ R, ‖b i‖^2) := by
  obtain ⟨A₁,hA₁,hSynthesis⟩ := SelbergPrimeOperator.uniform_prime_synthesis (ι := ι) B hB
  obtain ⟨A₂,hA₂,hBudget⟩ := SelbergLogarithmicBudget.budget_bound B C
  refine ⟨max A₁ A₂,hA₁.trans (le_max_left _ _),?_⟩
  intro A hA R τ hSep hHeight hCard P hP b
  have hCut₁ : A₁ ≤ A := (le_max_left _ _).trans hA
  have hCut₂ : A₂ ≤ A := (le_max_right _ _).trans hA
  have hA8 : 8 ≤ A := hA₁.trans hCut₁
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hA1P : 1 < A := by linarith only [hA8]
  let η := SelbergLogarithmicBudget.exponent B
  let Z := PowerSelbergLevel.level η A
  have hη : 0 < η ∧ η ≤ 1/32 ∧ 4*η ≤ UniformSelbergKernelEnvelope.decay B/2 :=
    SelbergLogarithmicBudget.exponent_bounds B
  have hZ : 1 ≤ Z := PowerSelbergLevel.level_pos η A hη.1.le hA1
  have hScale : (Z : ℝ)^2 ≤ Real.sqrt A := PowerSelbergLevel.level_square_bound η A (by linarith only [hη.2.1]) hA1
  have hZlt : (Z : ℝ) < A := PowerSelbergLevel.level_lt_scale η A (by linarith only [hη.2.1]) hA1P
  have hPrimes : ∀ p ∈ P, p.Prime ∧ Z < p ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A := by
    intro p hp
    obtain ⟨hpp,hLower,hUpper⟩ := hP p hp
    exact ⟨hpp,by exact_mod_cast hZlt.trans_le hLower,hLower,hUpper⟩
  have hActual := hSynthesis A hCut₁ Z hZ hScale R τ b hSep hHeight P hPrimes
  have hScalar := hBudget A hCut₂ R.card hCard
  calc
    _ ≤ (Real.exp 2*SelbergPrimeOperator.budget A B Z R.card)*(∑ i ∈ R, ‖b i‖^2) := hActual
    _ ≤ (Real.exp 2*(SelbergLogarithmicBudget.constant B*A/Real.log A))*(∑ i ∈ R, ‖b i‖^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScalar (Real.exp_pos 2).le)
        (sum_nonneg (fun _ _ ↦ sq_nonneg _))
    _ = _ := by unfold constant; ring

theorem uniform_analysis {ι : Type*} (B C : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ R : Finset ι, ∀ τ : ι → ℝ,
      (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
      (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
      (R.card : ℝ) ≤ (Real.log A)^C →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) → ∀ a : ℕ → ℂ,
      (∑ i ∈ R, ‖∑ p ∈ P, a p*LogarithmicExponentialSum.function (τ i) p‖^2) ≤
        (constant B*A/Real.log A)*(∑ p ∈ P, ‖a p‖^2) := by
  obtain ⟨A₁,hA₁,hAnalysis⟩ := SelbergPrimeOperator.uniform_prime_analysis (ι := ι) B hB
  obtain ⟨A₂,hA₂,hBudget⟩ := SelbergLogarithmicBudget.budget_bound B C
  refine ⟨max A₁ A₂,hA₁.trans (le_max_left _ _),?_⟩
  intro A hA R τ hSep hHeight hCard P hP a
  have hCut₁ : A₁ ≤ A := (le_max_left _ _).trans hA
  have hCut₂ : A₂ ≤ A := (le_max_right _ _).trans hA
  have hA8 : 8 ≤ A := hA₁.trans hCut₁
  have hA1 : 1 ≤ A := by linarith only [hA8]
  have hA1P : 1 < A := by linarith only [hA8]
  let η := SelbergLogarithmicBudget.exponent B
  let Z := PowerSelbergLevel.level η A
  have hη : 0 < η ∧ η ≤ 1/32 ∧ 4*η ≤ UniformSelbergKernelEnvelope.decay B/2 :=
    SelbergLogarithmicBudget.exponent_bounds B
  have hZ : 1 ≤ Z := PowerSelbergLevel.level_pos η A hη.1.le hA1
  have hScale : (Z : ℝ)^2 ≤ Real.sqrt A := PowerSelbergLevel.level_square_bound η A (by linarith only [hη.2.1]) hA1
  have hZlt : (Z : ℝ) < A := PowerSelbergLevel.level_lt_scale η A (by linarith only [hη.2.1]) hA1P
  have hPrimes : ∀ p ∈ P, p.Prime ∧ Z < p ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A := by
    intro p hp
    obtain ⟨hpp,hLower,hUpper⟩ := hP p hp
    exact ⟨hpp,by exact_mod_cast hZlt.trans_le hLower,hLower,hUpper⟩
  have hActual := hAnalysis A hCut₁ Z hZ hScale R τ hSep hHeight P hPrimes a
  have hScalar := hBudget A hCut₂ R.card hCard
  calc
    _ ≤ (Real.exp 2*SelbergPrimeOperator.budget A B Z R.card)*(∑ p ∈ P, ‖a p‖^2) := hActual
    _ ≤ (Real.exp 2*(SelbergLogarithmicBudget.constant B*A/Real.log A))*(∑ p ∈ P, ‖a p‖^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScalar (Real.exp_pos 2).le)
        (sum_nonneg (fun _ _ ↦ sq_nonneg _))
    _ = _ := by unfold constant; ring
end PaperP1.PrimeHalaszLogarithmicSamples
