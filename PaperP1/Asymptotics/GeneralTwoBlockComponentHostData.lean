module

public import PaperP1.Arithmetic.TwoBlockComponentPatterns
public import PaperP1.Asymptotics.SmoothGeneralNonalignedHostCount

/-! # General actual nontrivial components construct both root sets and smooth coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralTwoBlockComponentHostData

open Finset PaperP1.Arithmetic PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution
  PaperP1.LargePrimeGraphResolution PaperP1.TwoBlockComponentSquares PaperP1.TwoBlockComponentPatterns
  PaperP1.GeneralSplitRadicalPatternPool PaperP1.SplitRadicalPointHeight PaperP1.DefectivePredicate

local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

theorem offsets_nonempty {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : c ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) :
    (leftOffsets x y L c).Nonempty ∧ (rightOffsets x y L c).Nonempty := by
  obtain ⟨i, j, hi, hj⟩ :=
    LargePrimeComponentArithmetic.free_nontrivial_component_meets_both_blocks hx hy c hc
  have hleft : i ∈ (vertices x y L c).toLeft := mem_toLeft.mpr
    ((MediumPrimeColumns.mem_componentVertices _ c (Sum.inl i)).mpr hi)
  have hright : j ∈ (vertices x y L c).toRight := mem_toRight.mpr
    ((MediumPrimeColumns.mem_componentVertices _ c (Sum.inr j)).mpr hj)
  exact ⟨⟨_, mem_image.mpr ⟨i, hleft, rfl⟩⟩, ⟨_, mem_image.mpr ⟨j, hright, rfl⟩⟩⟩

theorem total_card (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (leftOffsets x y L c).card + (rightOffsets x y L c).card = (vertices x y L c).card := by
  rw [left_card, right_card, card_toLeft_add_card_toRight]

theorem square_roots {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) :
    ∃ w : ℤ, w ^ 2 = (((oddPrimeSupport (product x y L c)).prod id : ℕ) : ℤ) *
      integerProduct (leftOffsets x y L c) (x : ℤ) * integerProduct (rightOffsets x y L c) (y : ℤ) := by
  have hs := square_prescription hx hy c
  rw [product_eq (by omega : 1 ≤ x) (by omega : 1 ≤ y)] at hs
  obtain ⟨w, hw⟩ := hs
  exact ⟨w, by simpa only [pow_two, mul_assoc] using hw.symm⟩

theorem exists_pattern (k K x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : Fin k → (largePrimeGraph x y L).ConnectedComponent) (hcinj : Function.Injective c)
    (hfree : ∀ i, c i ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L))
    (hK : ∀ i, (vertices x y L (c i)).card ≤ K) :
    ∃ q ∈ pool k L (10 * (L + 1)) K, SmoothGeneralNonalignedHostCount.Valid K q ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * integerProduct (q.1.2 i) (y : ℤ) := by
  classical
  let q : Pattern k := ((fun i ↦ leftOffsets x y L (c i), fun i ↦ rightOffsets x y L (c i)),
    fun i ↦ oddPrimeSupport (product x y L (c i)))
  have htotal (i) : (leftOffsets x y L (c i)).card + (rightOffsets x y L (c i)).card ≤ K := by
    rw [total_card]
    exact hK i
  have hpool : q ∈ pool k L (10 * (L + 1)) K := by
    apply (mem_pool k L (10 * (L + 1)) K q).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (TwoBlockComponentPatterns.left_bound (c i)),
        (Nat.le_add_right _ _).trans (htotal i)⟩
    · intro i
      exact ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (TwoBlockComponentPatterns.right_bound (c i)),
        (Nat.le_add_left _ _).trans (htotal i)⟩
    · intro i
      exact support hx hy (c i) ((mem_nontrivialUnpinnedComponents _).mp (hfree i)).1
  have hboth (i) := offsets_nonempty (by omega : 1 ≤ x) (by omega : 1 ≤ y) (c i) (hfree i)
  refine ⟨q, hpool, ⟨?_, ?_, fun i ↦ (hboth i).1, fun i ↦ (hboth i).2, htotal⟩, ?_⟩
  · exact fun _ _ hne ↦ left_disjoint _ _ (fun h ↦ hne (hcinj h))
  · exact fun _ _ hne ↦ right_disjoint _ _ (fun h ↦ hne (hcinj h))
  · choose w hw using (fun i ↦ square_roots hx hy (c i))
    exact ⟨w, hw⟩

end PaperP1.GeneralTwoBlockComponentHostData
