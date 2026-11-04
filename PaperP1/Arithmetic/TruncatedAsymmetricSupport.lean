module

public import PaperP1.Arithmetic.TruncatedSubsetAnchor
public import PaperP1.Arithmetic.TruncatedAnchorPairs
public import PaperP1.Arithmetic.TranslatedKernelWindows
public import PaperP1.Arithmetic.TwoDefectCount

/-! # A literal sparse support cover for arbitrary old selections and at least two new values

Evenness is not needed once two distinct new values are selected. The
old selection may be empty, and then the new values are all defective.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedAsymmetricSupport

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEvenLoss PaperP1.LargeOddKernel
  PaperP1.TranslatedKernelWindows PaperP1.ForwardSubsetSelections

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Related (H x y : ℕ) : Prop :=
  ∃ A I : Finset ℕ, A ⊆ Ico (x - 1) (x - 1 + H) ∧ I ⊆ Ico (y - 1) (y - 1 + H) ∧
    2 ≤ I.card ∧ (∑ n ∈ A, largeParity H n) = ∑ n ∈ I, largeParity H n

def population (N H U : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico U (U + N)) ×ˢ (Ico U (U + N))).filter fun p ↦ Related H p.1 p.2

def defectStarts (N H U : ℕ) : Finset ℕ :=
  (Ico U (U + N)).filter fun y ↦ y - 1 ∈ TwoDefectHosts.twoDefectStarts H H (2 * N)

theorem alternative {N H U x y : ℕ} (T : ℝ) (hU : 2 ≤ U) (hUN : U ≤ N)
    (hx : x ∈ Ico U (U + N)) (hy : y ∈ Ico U (U + N)) (hrel : Related H x y) :
    (x, y) ∈ TruncatedAnchorPairs.bothPairs N H U T ∨
      x ∈ oneStarts N H U T ∧ y ∈ twoStarts N H U T ∨ y ∈ defectStarts N H U := by
  obtain ⟨A, I, hA, hI, hcard, he⟩ := hrel
  by_cases hlarge : ∃ n ∈ A ∪ I, T < (largeOddKernel H n : ℝ)
  · obtain ⟨n, hn, hT⟩ := hlarge
    rcases mem_union.mp hn with hnA | hnI
    · obtain ⟨i, hei, _hi⟩ := index_of_mem (x - 1) H A hA hnA
      apply Or.inl
      apply mem_union_left
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, i, by simpa only [hei] using hT,
        TruncatedSubsetAnchor.of_subsets hA hI he i (by simpa only [hei] using hnA)⟩
    · obtain ⟨i, hei, _hi⟩ := index_of_mem (y - 1) H I hI hnI
      apply Or.inl
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨(y, x), mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, i,
        by simpa only [hei] using hT,
        TruncatedSubsetAnchor.of_subsets hI hA he.symm i (by simpa only [hei] using hnI)⟩, rfl⟩
  · have hsmall (n : ℕ) (hn : n ∈ A ∪ I) : (largeOddKernel H n : ℝ) ≤ T :=
      le_of_not_gt (fun hh ↦ hlarge ⟨n, hn, hh⟩)
    obtain ⟨n, hn, m, hm, hnm⟩ := one_lt_card.mp (show 1 < I.card by omega)
    obtain ⟨i, hei, _hi⟩ := index_of_mem (y - 1) H I hI hn
    obtain ⟨j, hej, _hj⟩ := index_of_mem (y - 1) H I hI hm
    have hij : i ≠ j := by intro hh; apply hnm; rw [← hei, ← hej, hh]
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      obtain ⟨k, hek, _hk⟩ := index_of_mem (x - 1) H A hA ha
      refine Or.inr (Or.inl ⟨mem_filter.mpr ⟨hx, k, ?_⟩, mem_filter.mpr ⟨hy, i, j, hij, ?_, ?_⟩⟩)
      · simpa only [hek] using hsmall a (mem_union_left I ha)
      · simpa only [hei] using hsmall n (mem_union_right A hn)
      · simpa only [hej] using hsmall m (mem_union_right A hm)
    · have hempty : A = ∅ := not_nonempty_iff_eq_empty.mp hAne
      have hzero : (∑ a ∈ I, largeParity H a) = 0 := by simpa only [hempty, sum_empty] using he.symm
      have hnD := TruncatedSubsetAnchor.defective_of_zero_subset hI hzero hn
      have hmD := TruncatedSubsetAnchor.defective_of_zero_subset hI hzero hm
      apply Or.inr
      apply Or.inr
      apply mem_filter.mpr
      refine ⟨hy, TwoDefectHosts.mem_twoDefectStarts.mpr ⟨?_, ?_, i.val, ?_, j.val, ?_, ?_, ?_, ?_⟩⟩
      · have hh := (mem_Ico.mp hy).1; omega
      · have hh := (mem_Ico.mp hy).2; omega
      · exact i.isLt.le
      · exact j.isLt.le
      · exact fun hh ↦ hij (Fin.ext hh)
      · simpa only [hei] using hnD
      · simpa only [hej] using hmD

theorem population_subset (N H U : ℕ) (T : ℝ) (hU : 2 ≤ U) (hUN : U ≤ N) :
    population N H U ⊆
      (TruncatedAnchorPairs.bothPairs N H U T ∪ (oneStarts N H U T ×ˢ twoStarts N H U T)) ∪
        (Ico U (U + N) ×ˢ defectStarts N H U) := by
  intro p hp
  obtain ⟨hpblock, hrel⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hpblock
  rcases alternative T hU hUN hx hy hrel with hlarge | hsmall | hdefect
  · exact mem_union_left _ (mem_union_left _ hlarge)
  · exact mem_union_left _ (mem_union_right _ (mem_product.mpr hsmall))
  · exact mem_union_right _ (mem_product.mpr ⟨hx, hdefect⟩)

theorem population_card (N H U : ℕ) (T : ℝ) (hU : 2 ≤ U) (hUN : U ≤ N) :
    (population N H U).card ≤ (TruncatedAnchorPairs.bothPairs N H U T).card +
      (oneStarts N H U T).card * (twoStarts N H U T).card + N * (defectStarts N H U).card := by
  have hh := (card_le_card (population_subset N H U T hU hUN)).trans (card_union_le _ _)
  have hl := card_union_le (TruncatedAnchorPairs.bothPairs N H U T) (oneStarts N H U T ×ˢ twoStarts N H U T)
  rw [card_product] at hl
  rw [card_product, Nat.card_Ico] at hh
  have he : U + N - U = N := by omega
  rw [he] at hh
  omega

theorem defect_card (N H U : ℕ) (hU : 2 ≤ U) :
    (defectStarts N H U).card ≤ (TwoDefectHosts.twoDefectStarts H H (2 * N)).card := by
  apply card_le_card_of_injOn (fun y ↦ y - 1)
  · intro y hy
    exact (mem_filter.mp hy).2
  · intro x hx y hy he
    have hxlo := (mem_Ico.mp (mem_filter.mp hx).1).1
    have hylo := (mem_Ico.mp (mem_filter.mp hy).1).1
    change x - 1 = y - 1 at he
    omega

end PaperP1.TruncatedAsymmetricSupport
