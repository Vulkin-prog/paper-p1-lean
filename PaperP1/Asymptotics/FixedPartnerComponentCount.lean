module

public import PaperP1.Asymptotics.FixedPartnerPatternCount
public import PaperP1.Asymptotics.GeneralTwoBlockComponentHostData

/-! # The last actual graph consequence of T1.7 is unconditional

A free component with at least two target vertices constructs its literal
single-variable square equation. The actual component and all its smooth
coefficients and offset sets are included in the proved finite enumeration.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPartnerComponentCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution
  PaperP1.LargePrimeGraphResolution
  PaperP1.TwoBlockComponentSquares PaperP1.TwoBlockComponentPatterns
  PaperP1.GeneralTwoBlockComponentHostData PaperP1.GeneralSplitRadicalPatternPool
  PaperP1.SplitRadicalPointHeight PaperP1.DefectivePredicate

theorem component_pattern {x y L K : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c)
    (hsize : (vertices x y L c).card ≤ K) (hright : 2 ≤ (vertices x y L c).toRight.card) :
    ∃ q ∈ pool 1 L (10 * (L + 1)) K, 2 ≤ (q.1.2 0).card ∧
      IsSquare (coefficient q 0 * integerProduct (q.1.1 0) (x : ℤ) *
        integerProduct (q.1.2 0) (y : ℤ)) := by
  let q : Pattern 1 := ((fun _ ↦ leftOffsets x y L c, fun _ ↦ rightOffsets x y L c),
    fun _ ↦ oddPrimeSupport (product x y L c))
  have htotal : (leftOffsets x y L c).card + (rightOffsets x y L c).card ≤ K := by
    rw [total_card]
    exact hsize
  have hpool : q ∈ pool 1 L (10 * (L + 1)) K := by
    apply (mem_pool 1 L (10 * (L + 1)) K q).mpr
    refine ⟨fun _ ↦ ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (left_bound c), by dsimp only [q]; omega⟩,
      fun _ ↦ ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr (right_bound c), by dsimp only [q]; omega⟩,
      fun _ ↦ support hx hy c hfree⟩
  refine ⟨q, hpool, ?_, ?_⟩
  · change 2 ≤ (rightOffsets x y L c).card
    rwa [right_card]
  · have hs := square_prescription hx hy c
    rw [product_eq (by omega : 1 ≤ x) (by omega : 1 ≤ y)] at hs
    change IsSquare ((((oddPrimeSupport (product x y L c)).prod id : ℕ) : ℤ) *
      integerProduct (leftOffsets x y L c) (x : ℤ) * integerProduct (rightOffsets x y L c) (y : ℤ))
    simpa only [mul_assoc] using hs

theorem uniform_count (C : ℝ) (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      ∀ S : Finset ℕ, (∀ y ∈ S, y ∈ dyadicBlock N) →
      (∀ y ∈ S, ∃ c : (largePrimeGraph x y L).ConnectedComponent,
        ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c ∧
        (vertices x y L c).card ≤ K ∧ 2 ≤ (vertices x y L c).toRight.card) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := FixedPartnerPatternCount.uniform_count C 10 K ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x hx S hS hcomp
  apply h N hN L (10 * (L + 1)) hband le_rfl x hx S hS
  intro y hy
  obtain ⟨c, hfree, hsize, hright⟩ := hcomp y hy
  have hx2 : 2 ≤ x := (by omega : 2 ≤ N).trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := (by omega : 2 ≤ N).trans (mem_Ico.mp (hS y hy)).1
  exact component_pattern hx2 hy2 c hfree hsize hright

end PaperP1.FixedPartnerComponentCount
