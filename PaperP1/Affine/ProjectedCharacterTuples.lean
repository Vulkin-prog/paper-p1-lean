module

public import PaperP1.Affine.ProjectionDensity
public import PaperP1.Affine.CenteredFourier

/-! # Projected tuple counts as exact expectations of the old-space density -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedCharacterTuples

open Finset PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.ProjectionDensity

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

def sumValue (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂) (i : ι) (x : V) : ℝ :=
  ∑ n, realCharacter (L i n) x

def tuples (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂) :
    Finset (∀ i, κ i) := by
  classical
  exact univ.filter fun n ↦ (∑ i, L i (n i)) ∈ S

theorem product_expansion (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂) (x : V) :
    phi S x * (∏ i, sumValue L i x) =
      ∑ n : ∀ i, κ i, phi S x * realCharacter (∑ i, L i (n i)) x := by
  unfold sumValue
  rw [Fintype.prod_sum, mul_sum]
  apply sum_congr rfl
  intro n _
  rw [realCharacter_sum]

theorem mean_projected_product [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂) :
    finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ phi S x * ∏ i, sumValue L i x) =
      ((tuples S L).card : ℝ) := by
  classical
  simp_rw [product_expansion]
  rw [finiteExpectation_sum]
  simp_rw [mean_phi_character]
  simp [tuples]

theorem count_le_absolute_product [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂) :
    ((tuples S L).card : ℝ) ≤ finiteExpectation (uniformFiniteProbability V).weight
      (fun x ↦ phi S x * ∏ i, |sumValue L i x|) := by
  rw [← mean_projected_product S L]
  unfold finiteExpectation
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ ((uniformFiniteProbability V).weight_nonneg x)
  apply mul_le_mul_of_nonneg_left _ (phi_nonneg S x)
  simpa only [abs_prod] using le_abs_self (∏ i, sumValue L i x)

end PaperP1.ProjectedCharacterTuples
