module

public import PaperP1.Affine.ProjectedCharacterTuples
public import PaperP1.Probability.FiniteHolder
public import Mathlib.Data.Fintype.BigOperators

/-! # Holder's bound for actual projected character tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectionHolder

open Finset PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.ProjectionDensity
open PaperP1.ProjectedCharacterTuples

theorem projected_count_holder {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (L : ∀ i, κ i → V →ₗ[𝔽₂] 𝔽₂)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + Fintype.card ι / b = 1) :
    ((tuples S L).card : ℝ) ≤ (Fintype.card S : ℝ) ^ (1 - 1 / a) *
      ∏ i, (finiteExpectation (uniformFiniteProbability V).weight
        (fun x ↦ |sumValue L i x| ^ b)) ^ (1 / b) := by
  classical
  let F : Option ι → V → ℝ := fun j x ↦ j.elim ((phi S x) ^ a) (fun i ↦ |sumValue L i x| ^ b)
  let α : Option ι → ℝ := fun j ↦ j.elim (1 / a) (fun _ ↦ 1 / b)
  have hF : ∀ j ∈ (univ : Finset (Option ι)), ∀ x, 0 ≤ F j x := by
    intro j _ x
    cases j with
    | none => exact Real.rpow_nonneg (phi_nonneg S x) a
    | some i => exact Real.rpow_nonneg (abs_nonneg _) b
  have hα : ∀ j ∈ (univ : Finset (Option ι)), 0 ≤ α j := by
    intro j _
    cases j <;> dsimp [α] <;> positivity
  have hsum : (∑ j : Option ι, α j) = 1 := by
    simpa only [α, Fintype.sum_option, Option.elim_none, Option.elim_some, sum_const,
      card_univ, nsmul_eq_mul, mul_one_div] using hab
  have hh := PaperP1.FiniteHolder.weighted_geometric_holder
    (uniformFiniteProbability V).weight (uniformFiniteProbability V).weight_nonneg univ F α hF hα hsum
  have hleft : ∀ x, (∏ j : Option ι, (F j x) ^ α j) = phi S x * ∏ i, |sumValue L i x| := by
    intro x
    rw [Fintype.prod_option]
    have ha1 : a * (1 / a) = 1 := by field_simp
    have hb1 : b * (1 / b) = 1 := by field_simp
    change ((phi S x) ^ a) ^ (1 / a) * (∏ i, (|sumValue L i x| ^ b) ^ (1 / b)) = _
    rw [← Real.rpow_mul (phi_nonneg S x), ha1, Real.rpow_one]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [← Real.rpow_mul (abs_nonneg _), hb1, Real.rpow_one]
  have hright : (∏ j : Option ι, (finiteExpectation (uniformFiniteProbability V).weight (F j)) ^ α j) =
      (Fintype.card S : ℝ) ^ (1 - 1 / a) * ∏ i,
        (finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ |sumValue L i x| ^ b)) ^ (1 / b) := by
    rw [Fintype.prod_option]
    change (finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ (phi S x) ^ a)) ^ (1 / a) * _ = _
    rw [mean_phi_rpow_root S a ha]
    rfl
  simp only [hleft] at hh
  rw [hright] at hh
  exact (count_le_absolute_product S L).trans hh

end PaperP1.ProjectionHolder
