module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.CofactorSparseRegime
public import PaperP1.Analysis.SparseSupportedMeanValue

set_option autoImplicit false
@[expose] public noncomputable section
universe u752
namespace PaperP1.CofactorSparseMeanValue
open Finset PaperP1
open scoped Classical

theorem weighted_cofactor_uniform :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ p : ℕ, 1 ≤ p → (p : ℝ) ≤ (X : ℝ)^(1/16 : ℝ) →
      ∀ {ι : Type u752} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (X : ℝ) →
      (R.card : ℝ) ≤ (X : ℝ)^(1/200 : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico (X/p) (2*(X/p)) → ∀ P : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S
        (fun n ↦ f n/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)) (τ r)‖^2) ≤ 10*(1+Real.log (X : ℝ)) := by
  obtain ⟨N₀,_hN₀,hs⟩ := SparseSupportedMeanValue.weighted_supported_uniform.{u752}
  obtain ⟨X₀,hX₀,hreg⟩ := CofactorSparseRegime.uniform_regime N₀
  refine ⟨X₀,hX₀,?_⟩
  intro X hX p hp hpB ι R τ T hT hTX hR htau hsep S hS P f hf
  obtain ⟨hNcut,hN1,hheight,hcard,hNX⟩ := hreg X hX p hp hpB
  have hh := hs (X/p) hNcut R τ T hT (hTX.trans hheight) (hR.trans hcard) htau hsep S hS P f hf
  have hNp : (0 : ℝ) < ((X/p : ℕ) : ℝ) := by exact_mod_cast (show 0 < X/p by omega)
  have hNXR : (((X/p : ℕ) : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hNX
  have hl := Real.log_le_log hNp hNXR
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hl) (by norm_num : (0 : ℝ) ≤ 10))

theorem cofactor_uniform :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ p : ℕ, 1 ≤ p → (p : ℝ) ≤ (X : ℝ)^(1/16 : ℝ) →
      ∀ {ι : Type u752} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (X : ℝ) →
      (R.card : ℝ) ≤ (X : ℝ)^(1/200 : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico (X/p) (2*(X/p)) → ∀ f : ℕ → ℂ, (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S f (τ r)‖^2) ≤ 10*(1+Real.log (X : ℝ)) := by
  obtain ⟨X₀,hX₀,hs⟩ := weighted_cofactor_uniform.{u752}
  refine ⟨X₀,hX₀,?_⟩
  intro X hX p hp hpB ι R τ T hT hTX hR htau hsep S hS f hf
  have hh := hs X hX p hp hpB R τ T hT hTX hR htau hsep S hS ∅ f hf
  simpa only [PrimeDivisorWeights.count,PrimeDivisorWeights.factors,filter_empty,card_empty,
    zero_add,Nat.cast_one,div_one] using hh
end PaperP1.CofactorSparseMeanValue
