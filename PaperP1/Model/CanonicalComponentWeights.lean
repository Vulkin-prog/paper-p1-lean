module

public import PaperP1.Model.NoSingletonSeedCover

/-! # Exact actual size weights factor over the canonical original components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalComponentWeights

open Finset PaperP1.Model.InfiniteStarts PaperP1.ActualCanonicalComponents

theorem disjoint_blocks (L : ℕ) (I : Finset ℕ) : (↑(blocks L I) : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro C hC D hD hne
  exact (NoSingletonSeedCover.distinct_blocks L I C D hC hD hne).1

theorem sum_card (L : ℕ) (I : Finset ℕ) : (∑ C ∈ blocks L I, C.card) = I.card := by
  have h := card_biUnion (disjoint_blocks L I)
  rw [union_blocks] at h
  exact h.symm

theorem weighted_absolute_factor (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (u : ℝ) :
    u ^ I.card * |infiniteCenteredCoefficient L I| =
      ∏ C ∈ blocks L I, (u ^ C.card * |infiniteCenteredCoefficient L C|) := by
  rw [prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_card, absolute_factor L hL I]

end PaperP1.CanonicalComponentWeights
