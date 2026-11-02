module

public import PaperP1.Arithmetic.PositiveLineOffsetRoots
public import PaperP1.Asymptotics.PositiveLineSplitCount

/-! # Three disjoint transverse equations suffice on a positive rational line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeLineSplitCount

open Finset PaperP1.Arithmetic PaperP1.PositiveLineOffsetRoots PaperP1.LinearKernelFibres

theorem uniform_count (K d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L a b : ℕ, 0 < a → 0 < b → ∀ c : ℤ,
      ∀ x₀ y₀ : ℕ, 2 ≤ x₀ → 2 ≤ y₀ →
      Function.Injective (evenSquareClassMap x₀ L) →
      Disjoint (squareClassSpace x₀ L) (squareClassSpace y₀ L) →
      (b : ℤ) * y₀ = (a : ℤ) * x₀ + c →
      ∀ P Q : Fin 3 → Finset (Fin (L + 1)),
      (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint P →
      (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint Q →
      (∀ i, (P i).Nonempty ∧ (Q i).Nonempty ∧ (P i).card + (Q i).card ≤ d) →
      ∀ D : Fin 3 → ℤ, (∀ i, D i ≠ 0) → ∀ S : Finset (ℕ × ℕ),
      (∀ xy ∈ S, (b : ℤ) * xy.2 = (a : ℤ) * xy.1 + c ∧ ∀ i : Fin 3,
        (∀ u ∈ P i, 0 < (xy.1 : ℤ) + integerOffset u ∧ a * value xy.1 (integerOffset u) ≤ N ^ K) ∧
        (∀ v ∈ Q i, 0 < (xy.2 : ℤ) + integerOffset v ∧ b * value xy.2 (integerOffset v) ≤ N ^ K) ∧
        IsSquare (D i * ((∏ u ∈ P i, ((xy.1 : ℤ) + integerOffset u)) *
          (∏ v ∈ Q i, ((xy.2 : ℤ) + integerOffset v))))) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  classical
  obtain ⟨N₀, hN₀, hc⟩ := PositiveLineSplitCount.uniform_count K d ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L a b ha hb c x₀ y₀ hx₀ hy₀ hinj hdirect hline₀ P Q hP hQ hPQ D hD S hS
  obtain ⟨i, _hi, hi⟩ := exists_surviving ha hb c x₀ y₀ hx₀ hy₀ hinj hdirect hline₀
    (univ : Finset (Fin 3)) (by norm_num) (fun i ↦ coordinates (P i) (Q i))
    (coordinates_pairwise_disjoint univ P Q hP hQ)
  have hPi : (integerOffsets (P i)).Nonempty := (hPQ i).1.image integerOffset
  have hQi : (integerOffsets (Q i)).Nonempty := (hPQ i).2.1.image integerOffset
  have hdegree : (integerOffsets (P i)).card + (integerOffsets (Q i)).card ≤ d := by
    rw [integerOffsets, integerOffsets, card_image_of_injective _ (integerOffset_injective L),
      card_image_of_injective _ (integerOffset_injective L)]
    exact (hPQ i).2.2
  apply hc N hN a b ha hb c (integerOffsets (P i)) (integerOffsets (Q i)) hPi hQi hdegree
    (disjoint_scaled_images c (P i) (Q i) hi) (D i) (hD i) S
  intro xy hxy
  refine ⟨(hS xy hxy).1, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    exact ((hS xy hxy).2 i).1 v hv
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    exact ((hS xy hxy).2 i).2.1 v hv
  · have hprodP : (∏ u ∈ integerOffsets (P i), ((xy.1 : ℤ) + u)) =
        ∏ u ∈ P i, ((xy.1 : ℤ) + integerOffset u) := by
      rw [integerOffsets, prod_image (integerOffset_injective L).injOn]
    have hprodQ : (∏ v ∈ integerOffsets (Q i), ((xy.2 : ℤ) + v)) =
        ∏ v ∈ Q i, ((xy.2 : ℤ) + integerOffset v) := by
      rw [integerOffsets, prod_image (integerOffset_injective L).injOn]
    rw [hprodP, hprodQ]
    exact ((hS xy hxy).2 i).2.2

end PaperP1.ThreeLineSplitCount
