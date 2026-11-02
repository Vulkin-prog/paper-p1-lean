module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Literal physical support of a sparse linear combination -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearCombinationSupport

open Finset

variable {K J A : Type*} [DivisionRing K] [DecidableEq A]

theorem support_subset (v : J → (A →₀ K)) (c : J →₀ K) :
    (Finsupp.linearCombination K v c).support ⊆ c.support.biUnion (fun j ↦ (v j).support) := by
  classical
  intro a ha
  change a ∈ (c.sum (fun j k ↦ k • v j)).support at ha
  obtain ⟨j, hj, haj⟩ := mem_biUnion.mp (Finsupp.support_sum ha)
  exact mem_biUnion.mpr ⟨j, hj, Finsupp.support_smul haj⟩

theorem card_le (v : J → (A →₀ K)) (c : J →₀ K) (ℓ : ℕ)
    (h : ∀ j, (v j).support.card ≤ ℓ) :
    (Finsupp.linearCombination K v c).support.card ≤ ℓ * c.support.card := by
  classical
  calc
    _ ≤ (c.support.biUnion (fun j ↦ (v j).support)).card := card_le_card (support_subset v c)
    _ ≤ ∑ j ∈ c.support, (v j).support.card := card_biUnion_le
    _ ≤ ∑ _j ∈ c.support, ℓ := sum_le_sum (fun j _hj ↦ h j)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
      exact Nat.mul_comm _ _

end PaperP1.LinearCombinationSupport
