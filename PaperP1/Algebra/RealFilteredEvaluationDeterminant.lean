module

public import PaperP1.Algebra.TruncatedEvaluationDegreeBudget
public import PaperP1.Algebra.WeightedEvaluationDeterminant

/-! # Real filtered determinant bounds with repeated high-order remainder weights

Distinct slot indices give the triangular small-scale power even when all
remainder slots carry the same capped Taylor order.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealFilteredEvaluationDeterminant

open Finset WeightedEvaluationDeterminant TruncatedEvaluationDegreeBudget

theorem weighted_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (index : κ → ℕ) (hindex : Function.Injective index)
    (C : Fin n → κ → ℝ) (V : κ → Fin n → ℝ) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hC : ∀ i k, |C i k| ≤ K)
    (hV : ∀ k j, |V k j| ≤ δ ^ min (index k) (n - 1)) :
    |(evaluationMatrix C V).det| ≤
      (Fintype.card κ : ℝ) ^ n * K ^ n * (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2) := by
  have hprod (f : Fin n → κ) (hf : Function.Injective f) :
      (∏ i, δ ^ min (index (f i)) (n - 1)) ≤ δ ^ (n * (n - 1) / 2) := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact pow_le_pow_of_le_one hδ hδone (triangular_budget n (index ∘ f) (hindex.comp hf))
  have hh := WeightedEvaluationDeterminant.weighted_bound C V
    (fun k ↦ δ ^ min (index k) (n - 1)) K (δ ^ (n * (n - 1) / 2))
      hK (pow_nonneg hδ _) hC hV hprod
  simpa only [Fintype.card_fin] using hh

end PaperP1.RealFilteredEvaluationDeterminant
