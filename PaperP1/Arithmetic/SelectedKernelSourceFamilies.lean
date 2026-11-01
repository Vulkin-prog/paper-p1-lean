module

public import PaperP1.Arithmetic.LargeAnchorPairs
public import PaperP1.Arithmetic.SmallKernelWindows
public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Model.FiniteRademacher

/-! # Literal mixed rational-square relations and their selected kernel witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedKernelSourceFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.LargeOddKernel
open PaperP1.SelectedKernelWitness PaperP1.LargeAnchorPairs

local instance selectedKernelPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def MixedSquare (x y L : ℕ) (I J : Finset (Fin (L + 1))) : Prop :=
  I.Nonempty ∧ J.Nonempty ∧ IsSquare ((∏ i ∈ I, (startCompleteVertexLabel x L i : ℚ)) *
      ∏ j ∈ J, (startCompleteVertexLabel y L j : ℚ))

def HasLargeSelection (x y L : ℕ) (T : ℝ) : Prop :=
  ∃ I J : Finset (Fin (L + 1)), MixedSquare x y L I J ∧
    ((∃ i ∈ I, T < (largeOddKernel (L + 1) (startCompleteVertexLabel x L i) : ℝ)) ∨
      ∃ j ∈ J, T < (largeOddKernel (L + 1) (startCompleteVertexLabel y L j) : ℝ))

def separatedPairs (N L : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    (xy.1 + L ≤ xy.2 ∨ xy.2 + L ≤ xy.1) ∧ HasLargeSelection xy.1 xy.2 L T

def smallWindows (N L : ℕ) (T : ℝ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ ∃ i : Fin (L + 1),
    (largeOddKernel (L + 1) (startCompleteVertexLabel x L i) : ℝ) ≤ T

theorem square_parity_relation {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (I J : Finset (Fin (L + 1)))
    (hsquare : IsSquare ((∏ i ∈ I, (startCompleteVertexLabel x L i : ℚ)) *
      ∏ j ∈ J, (startCompleteVertexLabel y L j : ℚ))) :
    (∑ i ∈ I, parityVec (startCompleteVertexLabel x L i)) +
      (∑ j ∈ J, parityVec (startCompleteVertexLabel y L j)) = 0 := by
  let f : Fin (L + 1) ⊕ Fin (L + 1) → ℕ :=
    Sum.elim (startCompleteVertexLabel x L) (startCompleteVertexLabel y L)
  have hpos (v : Fin (L + 1) ⊕ Fin (L + 1)) (_hv : v ∈ I.disjSum J) : f v ≠ 0 := by
    cases v with
    | inl i => dsimp [f]; rw [startCompleteVertexLabel_eq_offset (by omega)]; omega
    | inr j => dsimp [f]; rw [startCompleteVertexLabel_eq_offset (by omega)]; omega
  have h := (sum_parityVec_zero_iff_rational_square (I.disjSum J) f hpos).mpr
    (by simpa only [prod_disjSum, f, Sum.elim_inl, Sum.elim_inr] using hsquare)
  simpa only [sum_disjSum, f, Sum.elim_inl, Sum.elim_inr] using h

theorem selection_sum {x L : ℕ} (hx : 0 < x) (I : Finset (Fin (L + 1))) :
    (∑ i : Fin (L + 1), (if i ∈ I then (1 : F₂) else 0) • parityVec (x - 1 + i.val)) =
      ∑ i ∈ I, parityVec (startCompleteVertexLabel x L i) := by
  calc
    _ = ∑ i : Fin (L + 1), if i ∈ I then parityVec (startCompleteVertexLabel x L i) else 0 := by
      apply sum_congr rfl
      intro i _
      split_ifs with hi <;> simp only [one_smul, zero_smul, startCompleteVertexLabel_eq_offset hx]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and]

theorem anchored_of_selection {x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (I J : Finset (Fin (L + 1)))
    (hparity : (∑ i ∈ I, parityVec (startCompleteVertexLabel x L i)) +
      (∑ j ∈ J, parityVec (startCompleteVertexLabel y L j)) = 0)
    (i : Fin (L + 1)) (hi : i ∈ I) : AnchoredRelation (x - 1) (y - 1) (L + 1) i := by
  refine ⟨(fun i ↦ if i ∈ I then 1 else 0), (fun j ↦ if j ∈ J then 1 else 0), ?_, ?_⟩
  · dsimp only
    rw [ite_eq_left hi]
    exact one_ne_zero
  · rw [selection_sum hx I, selection_sum hy J]
    exact hparity

theorem source_pairs_subset {N L : ℕ} (T : ℝ) (hN : 2 ≤ N) :
    separatedPairs N L T ⊆ bothPairs N (L + 1) T := by
  intro xy hxy
  obtain ⟨hblock, _, I, J, hmixed, hlarge⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hx2 : 2 ≤ xy.1 := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ xy.2 := hN.trans (mem_Ico.mp hy).1
  have hparity := square_parity_relation hx2 hy2 I J hmixed.2.2
  rcases hlarge with ⟨i, hi, hT⟩ | ⟨j, hj, hT⟩
  · apply mem_union.mpr
    left
    refine mem_filter.mpr ⟨hblock, i, ?_, anchored_of_selection (by omega) (by omega) I J hparity i hi⟩
    simpa only [startCompleteVertexLabel_eq_offset (by omega : 0 < xy.1)] using hT
  · apply mem_union.mpr
    right
    refine mem_image.mpr ⟨(xy.2, xy.1), ?_, Prod.swap_swap xy⟩
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, j, ?_,
      anchored_of_selection (by omega) (by omega) J I (by simpa only [add_comm] using hparity) j hj⟩
    simpa only [startCompleteVertexLabel_eq_offset (by omega : 0 < xy.2)] using hT

theorem small_windows_eq {N L : ℕ} (T : ℝ) (hN : 2 ≤ N) :
    smallWindows N L T = PaperP1.SmallKernelWindows.windows N (L + 1) T := by
  apply filter_congr
  intro x hx
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  simp only [startCompleteVertexLabel_eq_offset hxpos]

end PaperP1.SelectedKernelSourceFamilies
