module

public import PaperP1.Model.ExtensionJointFactor

/-! # Two actual source blocks interact through precisely the intersection of their effective spans -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BlockJointIntersection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts PaperP1.SubspaceFamilyRank

theorem exact_of_positive (L : ℕ) (hL : 0 < L) (E A : Finset ℕ) (hEA : Disjoint E A)
    (hq : 0 < infiniteJointMoment L (E ∪ A)) :
    infiniteJointMoment L (E ∪ A) = infiniteJointMoment L E * infiniteJointMoment L A *
      (2 ^ Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) E ⊓
        span (fun x ↦ squareClassSpace x L) A) : ℝ) := by
  let S := fun x ↦ squareClassSpace x L
  let : Fintype (span S E) := MinimalRelativeRelations.spanFintype S E
  have hqA : 0 < infiniteJointMoment L A :=
    hq.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L subset_union_right)
  have hA := infiniteJointMoment_exact_of_pos (A.sup fun x ↦ x + L) L A hL
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hqA
  have hfull := ExtensionJointFactor.exact_of_positive L hL E A hEA hq
  rw [RelativeIntersectionNullity.identity, pow_add] at hfull
  calc
    _ = infiniteJointMoment L E *
        (((∏ x ∈ A, infiniteMarginal x L) * (2 ^ relativeNullityOn S A : ℝ)) *
          (2 ^ Module.finrank F₂ ↥(span S E ⊓ span S A) : ℝ)) := by rw [hfull]; ring
    _ = _ := by rw [← hA]; ring

theorem upper_bound (L : ℕ) (hL : 0 < L) (E A : Finset ℕ) (hEA : Disjoint E A) :
    infiniteJointMoment L (E ∪ A) ≤ infiniteJointMoment L E * infiniteJointMoment L A *
      (2 ^ Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) E ⊓
        span (fun x ↦ squareClassSpace x L) A) : ℝ) := by
  by_cases hq : 0 < infiniteJointMoment L (E ∪ A)
  · exact (exact_of_positive L hL E A hEA hq).le
  · exact (le_of_not_gt hq).trans (mul_nonneg
      (mul_nonneg (infiniteJointMoment_nonneg L E) (infiniteJointMoment_nonneg L A)) (by positivity))

theorem finite_bound (L : ℕ) (hL : 0 < L) (P Q : Finset (Finset ℕ))
    (H : Finset (Finset ℕ × Finset ℕ)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ p ∈ H, p.1 ∈ P ∧ p.2 ∈ Q ∧ Disjoint p.1 p.2 ∧
      (2 ^ Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) p.1 ⊓
        span (fun x ↦ squareClassSpace x L) p.2) : ℝ) ≤ K) :
    (∑ p ∈ H, infiniteJointMoment L (p.1 ∪ p.2)) ≤
      K * (∑ e ∈ P, infiniteJointMoment L e) * ∑ f ∈ Q, infiniteJointMoment L f := by
  classical
  calc
    _ ≤ ∑ p ∈ H, K * infiniteJointMoment L p.1 * infiniteJointMoment L p.2 := by
      apply sum_le_sum
      intro p hp
      have h := hH p hp
      exact (upper_bound L hL p.1 p.2 h.2.2.1).trans
        ((mul_le_mul_of_nonneg_left h.2.2.2 (mul_nonneg (infiniteJointMoment_nonneg L p.1)
          (infiniteJointMoment_nonneg L p.2))).trans_eq (by ring))
    _ ≤ ∑ p ∈ P ×ˢ Q, K * infiniteJointMoment L p.1 * infiniteJointMoment L p.2 :=
      sum_le_sum_of_subset_of_nonneg (fun p hp ↦ mem_product.mpr ⟨(hH p hp).1, (hH p hp).2.1⟩)
        (fun p _ _ ↦ mul_nonneg (mul_nonneg hK (infiniteJointMoment_nonneg L p.1))
          (infiniteJointMoment_nonneg L p.2))
    _ = ∑ e ∈ P, (K * infiniteJointMoment L e) * ∑ f ∈ Q, infiniteJointMoment L f := by
      rw [sum_product]
      apply sum_congr rfl
      intro e _
      rw [mul_sum]
    _ = _ := by rw [← sum_mul, ← mul_sum]

end PaperP1.BlockJointIntersection
