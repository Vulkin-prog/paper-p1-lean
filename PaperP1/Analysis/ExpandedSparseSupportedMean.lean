module

public import PaperP1.Analysis.SparseSupportedMeanValue
public import PaperP1.Analysis.ExpandedSparseGramEnvelope
public import PaperP1.Analysis.ExpandedSparseIntegerMean

set_option autoImplicit false
@[expose] public noncomputable section
universe u819
namespace PaperP1.ExpandedSparseSupportedMean
open Finset PaperP1
open scoped Classical

theorem supported_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u819} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ ExpandedSparseGramEnvelope.height N →
      (R.card : ℝ) ≤ ExpandedSparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico N (2*N) → ∀ f : ℕ → ℂ, (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S f (τ r)‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := ExpandedSparseIntegerMean.dirichlet_unit_uniform.{u819}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep S hS f hf
  have hb (n : ℕ) : ‖if n ∈ S then f n else (0 : ℂ)‖ ≤ 1 := by
    by_cases hn : n ∈ S
    · simpa only [ite_eq_left hn] using hf n hn
    · simp [hn]
  have hh := hs N hN R τ T hT hTU hR htau hsep (fun n ↦ if n ∈ S then f n else 0) (fun n _hn ↦ hb n)
  simp_rw [SparseSupportedMeanValue.support_value_identity N S hS f]
  exact hh

theorem weighted_supported_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u819} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ ExpandedSparseGramEnvelope.height N →
      (R.card : ℝ) ≤ ExpandedSparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico N (2*N) → ∀ P : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S
        (fun n ↦ f n/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)) (τ r)‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := supported_uniform.{u819}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep S hS P f hf
  exact hs N hN R τ T hT hTU hR htau hsep S hS _
    (fun n hn ↦ SparseSupportedMeanValue.count_coefficient_bound P f n (hf n hn))
end PaperP1.ExpandedSparseSupportedMean
