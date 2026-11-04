module

public import PaperP1.Combinatorics.DistinguishedPairWeights

/-! # Union fibers of arbitrary ordered finite-set pairs

Overlap is allowed. Each vertex has at most four membership patterns.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairUnionWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem fiber_card (P : Finset (Finset ι × Finset ι)) (I : Finset ι) :
    (P.filter fun p ↦ p.1 ∪ p.2 = I).card ≤ 4 ^ I.card := by
  have hsub : (P.filter fun p ↦ p.1 ∪ p.2 = I) ⊆ I.powerset ×ˢ I.powerset := by
    intro p hp
    have he := (mem_filter.mp hp).2
    apply mem_product.mpr
    constructor
    · apply mem_powerset.mpr
      rw [← he]
      exact subset_union_left
    · apply mem_powerset.mpr
      rw [← he]
      exact subset_union_right
  calc
    _ ≤ (I.powerset ×ˢ I.powerset).card := card_le_card hsub
    _ = (2 ^ I.card) * (2 ^ I.card) := by rw [card_product, card_powerset]
    _ = _ := by rw [← mul_pow]; norm_num

theorem weighted_bound (P : Finset (Finset ι × Finset ι)) (w : Finset ι → ℝ)
    (hw : ∀ I, 0 ≤ w I) :
    (∑ p ∈ P, w (p.1 ∪ p.2)) ≤
      ∑ I ∈ P.image (fun p ↦ p.1 ∪ p.2), (4 : ℝ) ^ I.card * w I := by
  have hsplit := sum_fiberwise_of_maps_to
    (s := P) (t := P.image (fun p ↦ p.1 ∪ p.2)) (g := fun p ↦ p.1 ∪ p.2)
    (fun p hp ↦ mem_image.mpr ⟨p, hp, rfl⟩) (fun p ↦ w (p.1 ∪ p.2))
  rw [← hsplit]
  apply sum_le_sum
  intro I _hI
  calc
    _ = ((P.filter fun p ↦ p.1 ∪ p.2 = I).card : ℝ) * w I := by
      calc
        _ = ∑ _p ∈ P.filter (fun p ↦ p.1 ∪ p.2 = I), w I :=
          sum_congr rfl (fun p hp ↦ by rw [(mem_filter.mp hp).2])
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_card P I) (hw I)

end PaperP1.PairUnionWeights
