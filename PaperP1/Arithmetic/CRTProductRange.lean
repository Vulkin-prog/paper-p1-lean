module

public import PaperP1.Arithmetic.CRTProductCover
public import PaperP1.Analysis.FiniteCRTTails

/-! # The cubic CRT count after summing over actual products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CRTProductRange

open Finset PaperP1.CRTProductCover

def centres (k : ℕ) (U : Fin 3 → ℕ) (N R : ℕ) (S : Finset ℕ) : Finset (Fin 3 → ℕ) :=
  S.biUnion fun Q ↦ productCentres k 3 U N R Q

theorem mem_centres (k : ℕ) (U : Fin 3 → ℕ) (N R : ℕ) (S : Finset ℕ) (X : Fin 3 → ℕ) :
    X ∈ centres k U N R S ↔ ∃ Q ∈ S, X ∈ productCentres k 3 U N R Q := mem_biUnion

theorem finite_bound (k : ℕ) (U : Fin 3 → ℕ) (N R : ℕ) (S : Finset ℕ)
    (T V A : ℝ) (hT : 1 ≤ T) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hS : ∀ Q ∈ S, 0 < Q ∧ T < (Q : ℝ) ∧ (Q : ℝ) ≤ V)
    (hfactor : ∀ Q ∈ S, ((ProductFactorizations.pool k Q).card : ℝ) ≤ A) :
    ((centres k U N R S).card : ℝ) ≤
      A * (2 * R + 1 : ℕ) ^ (3 * k) * (8 * (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + 4 * V) := by
  have hsum : ((centres k U N R S).card : ℝ) ≤
      A * (2 * R + 1 : ℕ) ^ (3 * k) * ∑ Q ∈ S, ((N : ℝ) / Q + 1) ^ 3 := by
    calc
      _ ≤ ∑ Q ∈ S, ((productCentres k 3 U N R Q).card : ℝ) := by
        exact_mod_cast (card_biUnion_le : (centres k U N R S).card ≤ _)
      _ ≤ ∑ Q ∈ S, A * (2 * R + 1 : ℕ) ^ (3 * k) * ((N : ℝ) / Q + 1) ^ 3 := by
        apply sum_le_sum
        intro Q hQ
        exact (product_card k 3 U N R Q (hS Q hQ).1).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hfactor Q hQ) (by positivity)) (by positivity))
      _ = _ := by rw [mul_sum]
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (FiniteCRTTails.finite_cube_sum N T V (Nat.cast_nonneg N) hT hV S hS) (by positivity))

theorem uniform_bound (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ M ≥ N₀, ∀ (U : Fin 3 → ℕ) (N R : ℕ) (S : Finset ℕ)
      (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ Q ∈ S, 0 < Q ∧ T < (Q : ℝ) ∧ (Q : ℝ) ≤ V ∧ Q ≤ M ^ K) →
      ((centres k U N R S).card : ℝ) ≤
        (M : ℝ) ^ ε * (2 * R + 1 : ℕ) ^ (3 * k) *
          (8 * (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + 4 * V) := by
  obtain ⟨N₀, hN₀, hcount⟩ := ProductFactorizations.uniform_count k K ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro M hM U N R S T V hT hV hS
  apply finite_bound k U N R S T V ((M : ℝ) ^ ε) hT hV (by positivity)
  · intro Q hQ
    exact ⟨(hS Q hQ).1, (hS Q hQ).2.1, (hS Q hQ).2.2.1⟩
  · intro Q hQ
    exact hcount M hM Q (hS Q hQ).2.2.2

end PaperP1.CRTProductRange
