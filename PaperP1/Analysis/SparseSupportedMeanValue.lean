module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.SparseIntegerMeanValue
public import PaperP1.Analysis.SparseGramEnvelope
public import PaperP1.Arithmetic.PrimeDivisorWeights

set_option autoImplicit false
@[expose] public noncomputable section
universe u750
namespace PaperP1.SparseSupportedMeanValue
open Finset PaperP1
open scoped Classical

theorem support_value_identity (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N)) (f : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value S f t=
      DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ if n ∈ S then f n else 0) t := by
  have he : (Ico N (2*N)).filter (fun n ↦ n ∈ S)=S := by
    ext n
    simp only [mem_filter]
    exact ⟨And.right,fun hn ↦ ⟨hS hn,hn⟩⟩
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  calc
    _ = ∑ n ∈ Ico N (2*N), if n ∈ S then f n/(n : ℂ)*LogarithmicPhase.phase (-Real.log n) t else 0 := by
      rw [← sum_filter,he]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      by_cases hs : n ∈ S <;> simp [hs]

theorem supported_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u750} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ SparseGramEnvelope.height N →
      (R.card : ℝ) ≤ SparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico N (2*N) → ∀ f : ℕ → ℂ, (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S f (τ r)‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := SparseIntegerMeanValue.dirichlet_unit_uniform.{u750}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep S hS f hf
  have hb (n : ℕ) : ‖if n ∈ S then f n else (0 : ℂ)‖ ≤ 1 := by
    by_cases hn : n ∈ S
    · simpa only [ite_eq_left hn] using hf n hn
    · simp [hn]
  have hh := hs N hN R τ T hT hTU hR htau hsep (fun n ↦ if n ∈ S then f n else 0) (fun n _hn ↦ hb n)
  simp_rw [support_value_identity N S hS f]
  exact hh

theorem count_coefficient_bound (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) (hf : ‖f n‖ ≤ 1) :
    ‖f n/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_one (by positivity : (0 : ℝ) < (PrimeDivisorWeights.count P n+1 : ℕ))).mpr
  exact hf.trans (by exact_mod_cast (show 1 ≤ PrimeDivisorWeights.count P n+1 by omega))

theorem weighted_supported_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u750} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ SparseGramEnvelope.height N →
      (R.card : ℝ) ≤ SparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ S : Finset ℕ, S ⊆ Ico N (2*N) → ∀ P : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n ∈ S, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S
        (fun n ↦ f n/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)) (τ r)‖^2) ≤ 10*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := supported_uniform.{u750}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep S hS P f hf
  exact hs N hN R τ T hT hTU hR htau hsep S hS _
    (fun n hn ↦ count_coefficient_bound P f n (hf n hn))
end PaperP1.SparseSupportedMeanValue
