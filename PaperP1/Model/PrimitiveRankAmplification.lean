module

public import PaperP1.Model.WeightedPrimitiveMass

/-! # Finite rank amplification without a cardinality-dependent constant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveRankAmplification

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteStarts PaperP1.WeightedPrimitiveMass

theorem mass_bound (F : Finset (Finset ℕ)) (L : ℕ) (u K : ℝ) (hu : 0 ≤ u)
    (hK : ∀ I ∈ F, (2 ^ PaperP1.Affine.relativeNullityOn
      (fun x ↦ squareClassSpace x L) I : ℝ) ≤ K) :
    rankMass F L u ≤ K * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L := by
  rw [mul_sum]
  apply sum_le_sum
  intro I hI
  have hnonneg : 0 ≤ u ^ I.card * ∏ x ∈ I, infiniteMarginal x L :=
    mul_nonneg (pow_nonneg hu I.card)
      (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have h := mul_le_mul_of_nonneg_left (hK I hI)
    hnonneg
  calc
    _ = (u ^ I.card * ∏ x ∈ I, infiniteMarginal x L) *
        (2 ^ PaperP1.Affine.relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) := by
      unfold PaperP1.PrimitiveWindowMass.weight
      ring
    _ ≤ (u ^ I.card * ∏ x ∈ I, infiniteMarginal x L) * K := h
    _ = _ := by rw [prod_mul_distrib, prod_const]; ring

end PaperP1.PrimitiveRankAmplification
