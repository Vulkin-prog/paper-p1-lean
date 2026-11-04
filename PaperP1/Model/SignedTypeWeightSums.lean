module

public import PaperP1.Model.SignedPrivateField

/-! # Summing exact heterogeneous signed type weights before geometric estimates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedTypeWeightSums

open Finset PaperP1.Arithmetic PaperP1.SignedExactWords PaperP1.SignedPrivateField

def typeWeight (L E : ℕ) : ℝ := ∑ t : Fin (E + 1) × F₂, signedMarkRate L t.1.val

theorem typeWeight_nonneg (L E : ℕ) : 0 ≤ typeWeight L E :=
  sum_nonneg (fun _ _ ↦ (signedMarkRate_pos _ _).le)

theorem typeWeight_le (L E : ℕ) : typeWeight L E ≤ (2 ^ L : ℝ)⁻¹ := by
  rw [typeWeight, Fintype.sum_prod_type,
    Fin.sum_univ_eq_sum_range (fun e ↦ ∑ _s : F₂, signedMarkRate L e)]
  exact sum_signedMarkRate_le L E

theorem pair_factorization {α τ : Type*} [Fintype α] [Fintype τ]
    (r : τ → ℝ) (W : α → α → ℝ) :
    (∑ a : α × τ, ∑ b : α × τ, r a.2 * r b.2 * W a.1 b.1) =
      (∑ t, r t) ^ 2 * (∑ j, ∑ k, W j k) := by
  simp only [Fintype.sum_prod_type]
  have hinner (j k : α) : (∑ s : τ, ∑ t : τ, r s * r t * W j k) =
      (∑ t, r t) ^ 2 * W j k := by
    simp only [mul_assoc, ← mul_sum, ← sum_mul, pow_two]
  calc
    _ = ∑ j : α, ∑ k : α, ∑ s : τ, ∑ t : τ, r s * r t * W j k := by
      apply sum_congr rfl
      intro j _
      rw [sum_comm]
    _ = (∑ t, r t) ^ 2 * (∑ j, ∑ k, W j k) := by
      simp only [hinner, ← mul_sum]

theorem sum_pairs {J : Finset ℕ} (L E : ℕ) (W : J → J → ℝ) :
    (∑ a : Index J E, ∑ b : Index J E,
      signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * W a.1 b.1) =
      (typeWeight L E) ^ 2 * (∑ j : J, ∑ k : J, W j k) :=
  pair_factorization (fun t : Fin (E + 1) × F₂ ↦ signedMarkRate L t.1.val) W

theorem sum_pairs_le {J : Finset ℕ} (L E : ℕ) (W : J → J → ℝ)
    (hW : ∀ j k, 0 ≤ W j k) :
    (∑ a : Index J E, ∑ b : Index J E,
      signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * W a.1 b.1) ≤
      ((2 ^ L : ℝ)⁻¹) ^ 2 * (∑ j : J, ∑ k : J, W j k) := by
  rw [sum_pairs]
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (typeWeight_nonneg L E) (typeWeight_le L E) 2
  · exact sum_nonneg (fun j _ ↦ sum_nonneg (fun k _ ↦ hW j k))

end PaperP1.SignedTypeWeightSums
