module

public import PaperP1.Combinatorics.PairUnionWeights

/-! # Bounded union fibers survive an injective encoding of ordered edge pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EncodedPairUnionWeights

open Finset

variable {α ι : Type*} [DecidableEq ι]

theorem weighted_bound (P : Finset α) (e f : α → Finset ι)
    (hinj : Set.InjOn (fun p ↦ (e p, f p)) P) (T : Finset (Finset ι)) (r : ℕ)
    (hhost : ∀ p ∈ P, e p ∪ f p ∈ T) (hcard : ∀ p ∈ P, (e p ∪ f p).card ≤ r)
    (w : Finset ι → ℝ) (hw : ∀ I, 0 ≤ w I) :
    (∑ p ∈ P, w (e p ∪ f p)) ≤ (4 : ℝ) ^ r * ∑ I ∈ T, w I := by
  let E := P.image (fun p ↦ (e p, f p))
  have hsum : (∑ p ∈ P, w (e p ∪ f p)) = ∑ q ∈ E, w (q.1 ∪ q.2) := by
    rw [sum_image hinj]
  have hsub : E.image (fun q ↦ q.1 ∪ q.2) ⊆ T := by
    intro I hI
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hI
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact hhost p hp
  calc
    _ ≤ ∑ I ∈ E.image (fun q ↦ q.1 ∪ q.2), (4 : ℝ) ^ I.card * w I :=
      hsum.trans_le (PairUnionWeights.weighted_bound E w hw)
    _ ≤ ∑ I ∈ E.image (fun q ↦ q.1 ∪ q.2), (4 : ℝ) ^ r * w I := by
      apply sum_le_sum
      intro I hI
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hI
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (hcard p hp)) (hw _)
    _ ≤ ∑ I ∈ T, (4 : ℝ) ^ r * w I :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) r) (hw I))
    _ = _ := by rw [mul_sum]

end PaperP1.EncodedPairUnionWeights
