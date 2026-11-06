module

public import PaperP1.Analysis.SeparatedGaussianBudget
public import PaperP1.Analysis.PositiveSelbergGram
public import PaperP1.Analysis.PrimeSelbergMajorant
public import PaperP1.Analysis.UniformSelbergKernelEnvelope


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SelbergPrimeOperator
open Finset Filter PaperP1
open scoped Classical

def budget (A B : ℝ) (Z m : ℕ) : ℝ :=
  (A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z)*SeparatedGaussianBudget.constant+
    (m : ℝ)*UniformSelbergKernelEnvelope.coefficient B*(Z : ℝ)^4*A^(1-UniformSelbergKernelEnvelope.decay B)

theorem budget_nonneg (A B : ℝ) (Z m : ℕ) (hA : 0 ≤ A) (hZ : 1 ≤ Z) : 0 ≤ budget A B Z m := by
  have hG := PrimeSelbergCoefficients.denominator_pos Z hZ
  have hL := SeparatedGaussianBudget.constant_pos
  have hC := UniformSelbergKernelEnvelope.coefficient_pos B
  unfold budget
  positivity

theorem uniform_energy_bound {ι : Type*} (B : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ Z : ℕ, 1 ≤ Z → (Z : ℝ)^2 ≤ Real.sqrt A →
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ b : ι → ℂ,
        (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
        (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
        PositiveSelbergGram.energy A Z R b τ ≤ budget A B Z R.card*(∑ i ∈ R, ‖b i‖^2) := by
  obtain ⟨A₀,hA₀,hKernel⟩ := UniformSelbergKernelEnvelope.uniform_bound B hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA Z hZ hScale R τ b hSep hHeight
  have hAP : 0 < A := by linarith only [hA₀.trans hA]
  have hG := PrimeSelbergCoefficients.denominator_pos Z hZ
  have hC := UniformSelbergKernelEnvelope.coefficient_pos B
  let M := A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator Z
  let E := UniformSelbergKernelEnvelope.coefficient B*(Z : ℝ)^4*A^(1-UniformSelbergKernelEnvelope.decay B)
  let K : ι → ι → ℝ := fun i j ↦ M*Real.exp (-(τ i-τ j)^2/4)+E
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hRow : ∀ i ∈ R, (∑ j ∈ R, K i j) ≤ budget A B Z R.card := by
    intro i hi
    calc
      _ = M*(∑ j ∈ R, Real.exp (-(τ i-τ j)^2/4))+(R.card : ℝ)*E := by
        dsimp only [K]
        rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
      _ ≤ M*SeparatedGaussianBudget.constant+(R.card : ℝ)*E :=
        add_le_add (mul_le_mul_of_nonneg_left (SeparatedGaussianBudget.row_bound R τ hSep i hi) hM) (le_refl _)
      _ = _ := by unfold budget; dsimp only [M,E]; ring
  have hQuadratic := FiniteSymmetricKernelBudget.symmetric_bound R (fun i ↦ ‖b i‖) K (budget A B Z R.card)
    (fun _ _ _ _ ↦ add_nonneg (mul_nonneg hM (Real.exp_pos _).le) hE) (by
      intro i hi j hj
      dsimp only [K]
      rw [show -(τ i-τ j)^2/4=-(τ j-τ i)^2/4 by ring]) hRow
  have hNorm := congrArg norm (PositiveSelbergGram.gram_identity A Z R b τ hAP)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (PositiveSelbergGram.energy_nonneg A Z R b τ)] at hNorm
  rw [hNorm]
  calc
    _ ≤ ∑ i ∈ R, ‖∑ j ∈ R, (b i*star (b j))*LognormalSelbergKernel.value A (τ i-τ j) Z‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ R, ∑ j ∈ R, ‖(b i*star (b j))*LognormalSelbergKernel.value A (τ i-τ j) Z‖ := by
      apply sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ = ∑ i ∈ R, ∑ j ∈ R, ‖LognormalSelbergKernel.value A (τ i-τ j) Z‖*‖b i‖*‖b j‖ := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [norm_mul,norm_mul,norm_star]
      ring
    _ ≤ ∑ i ∈ R, ∑ j ∈ R, K i j*‖b i‖*‖b j‖ := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hEnvelope : ‖LognormalSelbergKernel.value A (τ i-τ j) Z‖ ≤ K i j := by
        dsimp only [K,M,E]
        simpa only [neg_div] using hKernel A hA Z hZ hScale (τ i-τ j) (hHeight i hi j hj)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hEnvelope (norm_nonneg _)) (norm_nonneg _)
    _ ≤ _ := hQuadratic

theorem uniform_prime_synthesis {ι : Type*} (B : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ Z : ℕ, 1 ≤ Z → (Z : ℝ)^2 ≤ Real.sqrt A →
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ b : ι → ℂ,
        (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
        (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Z < p ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) →
        (∑ p ∈ P, ‖PositiveSelbergGram.polynomial R b τ p‖^2) ≤
          (Real.exp 2*budget A B Z R.card)*(∑ i ∈ R, ‖b i‖^2) := by
  obtain ⟨A₀,hA₀,hEnergy⟩ := uniform_energy_bound (ι := ι) B hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA Z hZ hScale R τ b hSep hHeight P hP
  have hAP : 0 < A := by linarith only [hA₀.trans hA]
  calc
    _ ≤ Real.exp 2*PositiveSelbergGram.energy A Z R b τ :=
      PrimeSelbergMajorant.prime_synthesis_bound A Z R b τ hAP hZ P hP
    _ ≤ Real.exp 2*(budget A B Z R.card*(∑ i ∈ R, ‖b i‖^2)) :=
      mul_le_mul_of_nonneg_left (hEnergy A hA Z hZ hScale R τ b hSep hHeight) (Real.exp_pos 2).le
    _ = _ := by ring

theorem uniform_prime_analysis {ι : Type*} (B : ℝ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ Z : ℕ, 1 ≤ Z → (Z : ℝ)^2 ≤ Real.sqrt A →
      ∀ R : Finset ι, ∀ τ : ι → ℝ,
        (∀ i ∈ R, ∀ j ∈ R, i ≠ j → 1 ≤ |τ i-τ j|) →
        (∀ i ∈ R, ∀ j ∈ R, |τ i-τ j| ≤ A^B) →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Z < p ∧ A ≤ p ∧ (p : ℝ) ≤ 2*A) →
        ∀ a : ℕ → ℂ,
        (∑ i ∈ R, ‖∑ p ∈ P, a p*LogarithmicExponentialSum.function (τ i) p‖^2) ≤
          (Real.exp 2*budget A B Z R.card)*(∑ p ∈ P, ‖a p‖^2) := by
  obtain ⟨A₀,hA₀,hSynthesis⟩ := uniform_prime_synthesis (ι := ι) B hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA Z hZ hScale R τ hSep hHeight P hP a
  have hAP : 0 < A := by linarith only [hA₀.trans hA]
  apply PrimeSelbergMajorant.analysis_of_synthesis P R a
    (fun i p ↦ LogarithmicExponentialSum.function (τ i) p) (Real.exp 2*budget A B Z R.card)
    (mul_nonneg (Real.exp_pos 2).le (budget_nonneg A B Z R.card hAP.le hZ))
  intro b
  exact hSynthesis A hA Z hZ hScale R τ b hSep hHeight P hP
end PaperP1.SelbergPrimeOperator
