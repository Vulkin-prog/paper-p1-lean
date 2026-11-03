module

public import PaperP1.Arithmetic.TernaryPrimeTopProducts
public import PaperP1.Arithmetic.CRTProductRange

/-! # The weak CRT count for actual individual-prime products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeCounts

open Finset PaperP1.TernaryPrimeTopProducts

theorem weak_uniform (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ M ≥ N₀, ∀ (F : Finset (Fin 3 → ℕ))
      (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ)
      (base : Fin 3 → ℕ) (N R : ℕ) (T V : ℝ), 1 ≤ T → 0 ≤ V →
      (∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + N)) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, ((n : ℤ) - X i).natAbs ≤ R) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) k : ℝ) ∧
        (topProduct (U X) (H X) k : ℝ) ≤ V ∧ topProduct (U X) (H X) k ≤ M ^ K) →
      (F.card : ℝ) ≤ (M : ℝ) ^ ε * (2 * R + 1 : ℕ) ^ (3 * k) *
        (8 * (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + 4 * V) := by
  obtain ⟨N₀, hN₀, hcount⟩ := CRTProductRange.uniform_bound k K ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro M hM F U H base N R T V hT hV hbox hoff hprod
  let S : Finset ℕ := F.image fun X ↦ topProduct (U X) (H X) k
  have hS : ∀ Q ∈ S, 0 < Q ∧ T < (Q : ℝ) ∧ (Q : ℝ) ≤ V ∧ Q ≤ M ^ K := by
    intro Q hQ
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hQ
    have hp := hprod X hX
    exact ⟨by exact_mod_cast lt_of_le_of_lt (by linarith : 0 ≤ T) hp.1, hp⟩
  have hsub : F ⊆ CRTProductRange.centres k base N R S := by
    intro X hX
    have hp : 0 < topProduct (U X) (H X) k := (hS _ (mem_image_of_mem _ hX)).1
    exact mem_biUnion.mpr ⟨_, mem_image_of_mem _ hX,
      top_product_certificate X hp (hoff X hX) base N (hbox X hX)⟩
  exact (show (F.card : ℝ) ≤ (CRTProductRange.centres k base N R S).card by
    exact_mod_cast card_le_card hsub).trans (hcount M hM base N R S T V hT hV hS)

end PaperP1.TernaryPrimeCounts
