module

public import PaperP1.Combinatorics.LargePrimeGraphResolution
public import PaperP1.Arithmetic.CriticalDefectPositions

/-! # Actual arithmetic interpretation of the large-prime graph

The cutoff is literally 10B, B=L+1. Formal vertex copies are retained even
when the two physical windows overlap. The number of defective graph vertices
equals the sum of the actual kernel-one counts on the two windows.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargePrimeComponentArithmetic

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model DefectivePredicate LargeOddKernel
open LargePrimeOccurrences LargePrimeGraph LargePrimeGraphResolution PinnedGraphResolution
open CriticalDefectPositions Finset

local instance componentArithmeticPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance componentArithmeticDecidableAdj (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

theorem isDefective_iff_intrinsic {x y L : ℕ} (v : Occurrence L) :
    IsDefective x y L v ↔ HDefective (10 * (L + 1)) (twoStartCompleteVertexLabel x y L v) := by
  constructor
  · intro h p hp hpH
    have hne : parityVec (twoStartCompleteVertexLabel x y L v) p ≠ 1 := by
      intro hone
      exact h p ⟨hp, hpH⟩ (mem_primeOccurrences.mpr hone)
    exact (show ∀ z : F₂, z ≠ 1 → z = 0 by decide) _ hne
  · intro h p hp hv
    have hz := h p hp.1 hp.2
    have hone := mem_primeOccurrences.mp hv
    rw [hz] at hone
    exact zero_ne_one hone

theorem isDefective_iff_kernel_one {x y L : ℕ} (v : Occurrence L) :
    IsDefective x y L v ↔ largeOddKernel (10 * (L + 1))
      (twoStartCompleteVertexLabel x y L v) = 1 :=
  (isDefective_iff_intrinsic v).trans (largeOddKernel_eq_one_iff _ _).symm

def defectiveIndices (x L : ℕ) : Finset (Fin (L + 1)) :=
  univ.filter fun i ↦ largeOddKernel (10 * (L + 1)) (startCompleteVertexLabel x L i) = 1

theorem defectiveVertexCount_eq_index_counts (x y L : ℕ) :
    defectiveVertexCount x y L = (defectiveIndices x L).card + (defectiveIndices y L).card := by
  classical
  have hset : defectiveVertices x y L = (defectiveIndices x L).disjSum (defectiveIndices y L) := by
    ext v
    cases v <;> simp [defectiveVertices, defectiveIndices, isDefective_iff_kernel_one,
      twoStartCompleteVertexLabel]
  rw [defectiveVertexCount, hset, card_disjSum]

theorem start_label_injective {x L : ℕ} (hx : 0 < x) :
    Function.Injective (startCompleteVertexLabel x L) := by
  intro i j hij
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hx] at hij
  exact Fin.ext (by omega)

theorem image_defectiveIndices {x L : ℕ} (hx : 0 < x) :
    (defectiveIndices x L).image (startCompleteVertexLabel x L) = criticalDefectivePositions x L := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hiK := (mem_filter.mp hi).2
    apply mem_criticalDefectivePositions.mpr
    rw [startCompleteVertexLabel_eq_offset hx]
    rw [startCompleteVertexLabel_eq_offset hx] at hiK
    exact ⟨by omega, by have := i.isLt; omega, hiK⟩
  · intro hn
    obtain ⟨hnlo, hnhi, hnK⟩ := mem_criticalDefectivePositions.mp hn
    let i : Fin (L + 1) := ⟨n - (x - 1), by omega⟩
    have hi : startCompleteVertexLabel x L i = n := by
      rw [startCompleteVertexLabel_eq_offset hx]
      dsimp [i]
      omega
    refine mem_image.mpr ⟨i, ?_, hi⟩
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simpa only [hi] using hnK⟩

theorem card_defectiveIndices {x L : ℕ} (hx : 0 < x) :
    (defectiveIndices x L).card = (criticalDefectivePositions x L).card := by
  rw [← image_defectiveIndices hx, card_image_of_injective _ (start_label_injective hx)]

theorem defectiveVertexCount_eq_actual_counts {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    defectiveVertexCount x y L = (criticalDefectivePositions x L).card +
      (criticalDefectivePositions y L).card := by
  rw [defectiveVertexCount_eq_index_counts, card_defectiveIndices hx, card_defectiveIndices hy]

theorem defectiveVertexCount_critical_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
        (defectiveVertexCount x y L : ℝ) ≤
          K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := uniform_critical_defect_constant
  refine ⟨2 * K, by positivity, fun C ↦ ?_⟩
  obtain ⟨N₁, hN₁⟩ := hbound C
  refine ⟨max 2 N₁, ?_⟩
  intro N hN L hband x hx y hy
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have h₁ := hN₁ N (by omega) L hband x hx
  have h₂ := hN₁ N (by omega) L hband y hy
  rw [defectiveVertexCount_eq_actual_counts hxpos hypos, Nat.cast_add]
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) +
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := add_le_add h₁ h₂
    _ = _ := by ring

theorem solution_constant_on_component {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (w : largePrimeSolution x y L) {v z : Occurrence L}
    (hcomp : (largePrimeGraph x y L).connectedComponentMk v =
      (largePrimeGraph x y L).connectedComponentMk z) : w.val v = w.val z := by
  have hw : w.val ∈ PinnedGraphSpace (largePrimeGraph x y L) (pinnedVertices x y L) := by
    rw [← largePrimeSolution_eq_pinnedGraphSpace hx hy]
    exact w.property
  exact eq_of_connectedComponentMk_eq (largePrimeGraph x y L) ⟨w.val, hw⟩ hcomp

theorem component_selected_or_omitted {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (w : largePrimeSolution x y L) (C : (largePrimeGraph x y L).ConnectedComponent) :
    (∀ v, (largePrimeGraph x y L).connectedComponentMk v = C → w.val v = 0) ∨
      (∀ v, (largePrimeGraph x y L).connectedComponentMk v = C → w.val v = 1) := by
  have hrep : (largePrimeGraph x y L).connectedComponentMk C.out = C := C.out_eq
  have hbinary : w.val C.out = 0 ∨ w.val C.out = 1 :=
    (show ∀ z : F₂, z = 0 ∨ z = 1 by decide) _
  rcases hbinary with hzero | hone
  · left
    intro v hv
    exact (solution_constant_on_component hx hy w (hv.trans hrep.symm)).trans hzero
  · right
    intro v hv
    exact (solution_constant_on_component hx hy w (hv.trans hrep.symm)).trans hone

theorem component_has_edge {x y L : ℕ}
    (C : (largePrimeGraph x y L).ConnectedComponent) (hsize : 2 ≤ Fintype.card C.supp) :
    ∃ v z : Occurrence L, (largePrimeGraph x y L).connectedComponentMk v = C ∧
      (largePrimeGraph x y L).Adj v z := by
  classical
  let v := C.out
  have hv : (largePrimeGraph x y L).connectedComponentMk v = C := C.out_eq
  have hedge : ∃ z, (largePrimeGraph x y L).Adj v z := by
    by_contra hno
    push Not at hno
    have hone : Fintype.card C.supp = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨v, ?_⟩, ?_⟩
      · simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv
      · intro z
        apply Subtype.ext
        have hz : (largePrimeGraph x y L).connectedComponentMk z.val = C := by
          simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using z.property
        exact eq_of_reachable_of_no_adj hno (SimpleGraph.ConnectedComponent.exact
          (hv.trans hz.symm))
    omega
  obtain ⟨z, hvz⟩ := hedge
  exact ⟨v, z, hv, hvz⟩

theorem component_card_two_le_of_edge {x y L : ℕ}
    (C : (largePrimeGraph x y L).ConnectedComponent) {v z : Occurrence L}
    (hv : (largePrimeGraph x y L).connectedComponentMk v = C)
    (hadj : (largePrimeGraph x y L).Adj v z) : 2 ≤ Fintype.card C.supp := by
  have hz : (largePrimeGraph x y L).connectedComponentMk z = C :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hv
  have hvSupp : v ∈ C.supp := by
    simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv
  have hzSupp : z ∈ C.supp := by
    simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff] using hz
  have hne : (⟨v, hvSupp⟩ : C.supp) ≠ ⟨z, hzSupp⟩ := by
    intro heq
    exact (largePrimeGraph_adj.mp hadj).1 (congrArg Subtype.val heq)
  exact Nat.succ_le_of_lt (Fintype.one_lt_card_iff.mpr ⟨⟨v, hvSupp⟩, ⟨z, hzSupp⟩, hne⟩)

theorem nontrivial_free_iff_unpinned_edge {x y L : ℕ}
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    IsNontrivialUnpinnedComponent (largePrimeGraph x y L) (pinnedVertices x y L) C ↔
      ¬ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) C ∧
        ∃ v z : Occurrence L, (largePrimeGraph x y L).connectedComponentMk v = C ∧
          (largePrimeGraph x y L).Adj v z := by
  constructor
  · rintro ⟨hpin, hsize⟩
    exact ⟨hpin, component_has_edge C hsize⟩
  · rintro ⟨hpin, v, z, hv, hadj⟩
    exact ⟨hpin, component_card_two_le_of_edge C hv hadj⟩

theorem nontrivial_component_meets_both_blocks {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent) (hsize : 2 ≤ Fintype.card C.supp) :
    ∃ i j : Fin (L + 1), (largePrimeGraph x y L).connectedComponentMk (Sum.inl i) = C ∧
      (largePrimeGraph x y L).connectedComponentMk (Sum.inr j) = C := by
  obtain ⟨v, z, hv, hvz⟩ := component_has_edge C hsize
  have hz : (largePrimeGraph x y L).connectedComponentMk z = C :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvz).symm.trans hv
  obtain ⟨hne, p, hp, hvp, hzp⟩ := largePrimeGraph_adj.mp hvz
  have hop := inOppositeBlocks_of_mem_of_ne hx hy hp.1 (largePrime_gt_length hp) hvp hzp hne
  rcases hop with ⟨i, j, hvi, hzj⟩ | ⟨j, i, hvj, hzi⟩
  · exact ⟨i, j,
      (congrArg (largePrimeGraph x y L).connectedComponentMk hvi).symm.trans hv,
      (congrArg (largePrimeGraph x y L).connectedComponentMk hzj).symm.trans hz⟩
  · exact ⟨i, j,
      (congrArg (largePrimeGraph x y L).connectedComponentMk hzi).symm.trans hz,
      (congrArg (largePrimeGraph x y L).connectedComponentMk hvj).symm.trans hv⟩

theorem free_nontrivial_component_meets_both_blocks {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC : C ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) :
    ∃ i j : Fin (L + 1), (largePrimeGraph x y L).connectedComponentMk (Sum.inl i) = C ∧
      (largePrimeGraph x y L).connectedComponentMk (Sum.inr j) = C :=
  nontrivial_component_meets_both_blocks hx hy C
    ((mem_nontrivialUnpinnedComponents (largePrimeGraph x y L)).mp hC).2

end PaperP1.LargePrimeComponentArithmetic
