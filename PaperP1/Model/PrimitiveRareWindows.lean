module

public import PaperP1.Model.PrimitiveSmallKernelDichotomy
public import PaperP1.Arithmetic.WindowSquareKernelBound
public import PaperP1.Arithmetic.SmallKernelWindowSets

/-! # Sparse large-coordinate support yields eleven actual small-kernel values with controlled square parts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveRareWindows

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.RankinSmallKernel
  PaperP1.NormalizedWindowSets PaperP1.PrimitiveSmallKernelDichotomy
  PaperP1.WindowSquareKernelBound PaperP1.Affine

def kernelValues (L : ℕ) (Y T : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact (PaperP1.NormalizedWindowSets.values x L).filter fun v ↦ (truncatedKernel Y v : ℝ) ≤ T

theorem small_offsets_card {L x : ℕ} (hx : 0 < x) (Y T : ℝ) :
    (smallOffsets L Y T x).card = (kernelValues L Y T x).card := by
  classical
  have himage : (smallOffsets L Y T x).image (startCompleteVertexLabel x L) = kernelValues L Y T x := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      exact mem_filter.mpr ⟨mem_values.mpr ⟨i, rfl⟩,
        by simpa only [startCompleteVertexLabel_eq_offset hx] using (mem_filter.mp hi).2⟩
    · intro hv
      obtain ⟨hvW, hvK⟩ := mem_filter.mp hv
      obtain ⟨i, rfl⟩ := mem_values.mp hvW
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _,
        by simpa only [startCompleteVertexLabel_eq_offset hx] using hvK⟩, rfl⟩
  rw [← himage, card_image_of_injective _ (startCompleteVertexLabel_injective hx)]

theorem many_small_values {N L x : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hscale : (3 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)) (hx : x ∈ dyadicBlock N)
    (Y β : ℝ) (hY : 0 ≤ Y)
    (hsmall : 12 ≤ (smallOffsets L Y ((N : ℝ) ^ β) x).card)
    (hout : x ∉ PaperP1.TwoSmallKernelWindows.windows N L (L + 1) ((N : ℝ) ^ (2 / 3 : ℝ))) :
    x ∈ PaperP1.SmallKernelWindowSets.severalWindows N L ⌊Y⌋₊ 11 β (2 / 3) := by
  classical
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  let A := kernelValues L Y ((N : ℝ) ^ β) x
  let B := PaperP1.SmallKernelWindowSets.smallValues N L ⌊Y⌋₊ x β (2 / 3)
  let D := largeSquareValues N L ⌊Y⌋₊ x
  have hA : 12 ≤ A.card := by simpa only [A, small_offsets_card hxpos] using hsmall
  have hD : D.card ≤ 1 := outside_two_kernel hN hL hscale hx hout
  have hcover : A ⊆ B ∪ D := by
    intro v hv
    obtain ⟨hvW, hvK⟩ := mem_filter.mp hv
    have hkernel : (PaperP1.LargeOddKernel.largeOddKernel ⌊Y⌋₊ v : ℝ) ≤ (N : ℝ) ^ β := by
      simpa only [PaperP1.RankinSmallKernel.truncatedKernel_eq_floor Y hY] using hvK
    by_cases hs : ((PaperP1.CutoffSquareParts.largeSquarePart ⌊Y⌋₊ v ^ 2 : ℕ) : ℝ) ≤
        (N : ℝ) ^ (2 / 3 : ℝ)
    · exact mem_union_left _ (mem_filter.mpr ⟨hvW, hkernel, hs⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hvW, lt_of_not_ge hs⟩)
  have hcard := (card_le_card hcover).trans (card_union_le B D)
  refine mem_filter.mpr ⟨hx, ?_⟩
  change 11 ≤ B.card
  omega

end PaperP1.PrimitiveRareWindows
