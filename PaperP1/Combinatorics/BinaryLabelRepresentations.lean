module

public import PaperP1.Combinatorics.ZeroSumFreeRepresentations
public import PaperP1.Affine.PairFourierIntersection

/-! # Minimal nonzero label representations extracted from physical supports

Repeated binary labels cancel. A minimal remaining representation is
zero-sum-free and has no zero label. The construction keeps the actual
label set and its physical cardinality bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLabelRepresentations

open Finset PaperP1.ZeroSumFreeRepresentations PaperP1.Affine

variable {W : Type*} [AddCommGroup W] [DecidableEq W]

theorem minimal_representation (S : Finset W) (α : W) (hα : α ≠ 0)
    (hsum : (∑ a ∈ S, a) = α) :
    ∃ A ⊆ S, A.Nonempty ∧ ZeroSumFree A ∧ (∑ a ∈ A, a) = α := by
  classical
  let F := S.powerset.filter fun A ↦ (∑ a ∈ A, a) = α
  have hSF : S ∈ F := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hsum⟩
  obtain ⟨A, hAF, hmin⟩ := exists_min_image F Finset.card ⟨S, hSF⟩
  obtain ⟨hAS, hsumA⟩ := mem_filter.mp hAF
  have hsub : A ⊆ S := mem_powerset.mp hAS
  have hne : A.Nonempty := by
    by_contra h
    have hzero : A = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [hzero, sum_empty] at hsumA
    exact hα hsumA.symm
  refine ⟨A, hsub, hne, ?_, hsumA⟩
  intro B hBA hsumB
  have hsumdiff : (∑ a ∈ A \ B, a) = α := by
    have h := sum_sdiff (f := id) hBA
    simpa only [id_eq, hsumB, add_zero, hsumA] using h
  have hdiff : A \ B ∈ F := mem_filter.mpr
    ⟨mem_powerset.mpr ((sdiff_subset).trans hsub), hsumdiff⟩
  have hsmall := hmin (A \ B) hdiff
  have hcard := card_sdiff_add_card_eq_card hBA
  exact card_eq_zero.mp (by omega)

omit [DecidableEq W] in
theorem zero_not_mem_of_zeroSumFree {S : Finset W} (hS : ZeroSumFree S) : (0 : W) ∉ S := by
  intro hz
  have h := hS {0} (singleton_subset_iff.mpr hz) (by simp)
  simp at h

variable {V : Type*} [DecidableEq V] [Module 𝔽₂ W]

theorem sum_subselection (L : V → W) (A : Finset V) :
    ∃ B ⊆ A.image L, (∑ b ∈ B, b) = ∑ v ∈ A, L v := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert v A hv ih =>
    obtain ⟨B, hB, hsum⟩ := ih
    have hsub : B ⊆ (insert v A).image L := hB.trans (image_mono L (subset_insert v A))
    by_cases hLv : L v ∈ B
    · refine ⟨B.erase (L v), (erase_subset _ _).trans hsub, ?_⟩
      rw [sum_insert hv]
      have herase := sum_erase_add B id hLv
      simp only [id_eq] at herase
      calc
        _ = ((∑ b ∈ B.erase (L v), b) + L v) + L v := by
          rw [add_assoc, PaperP1.PairFourierIntersection.self_add, add_zero]
        _ = (∑ b ∈ B, b) + L v := by rw [herase]
        _ = _ := by rw [hsum, add_comm]
    · refine ⟨insert (L v) B, ?_, ?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact mem_image.mpr ⟨v, mem_insert_self _ _, rfl⟩
        · exact hsub hb
      · rw [sum_insert hLv, sum_insert hv, hsum]

theorem physical_representation (L : V → W) (A : Finset V) (α : W) (hα : α ≠ 0)
    (hsum : (∑ v ∈ A, L v) = α) :
    ∃ B ⊆ A.image L, B.Nonempty ∧ ZeroSumFree B ∧ (0 : W) ∉ B ∧
      B.card ≤ A.card ∧ (∑ b ∈ B, b) = α := by
  obtain ⟨S, hS, hsumS⟩ := sum_subselection L A
  obtain ⟨B, hBS, hBne, hBfree, hsumB⟩ := minimal_representation S α hα (hsumS.trans hsum)
  have hBsub := hBS.trans hS
  exact ⟨B, hBsub, hBne, hBfree, zero_not_mem_of_zeroSumFree hBfree,
    (card_le_card hBsub).trans card_image_le, hsumB⟩

end PaperP1.BinaryLabelRepresentations
