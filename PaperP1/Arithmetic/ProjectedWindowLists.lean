module

public import PaperP1.Arithmetic.ShortProjectedLists
public import PaperP1.Arithmetic.AnchorKernelProduct
public import PaperP1.Combinatorics.FinTupleErasure
public import Mathlib.Algebra.BigOperators.Fin

/-! # Actual full-support window witnesses and preservation after deletion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedWindowLists

open Finset PaperP1.Arithmetic PaperP1.LinearKernelFibres
  PaperP1.BoundedIntegerMotifs PaperP1.OldSpaceProjection

def vector (x : ℕ) (A : Finset ℤ) : ℕ →₀ F₂ := ∑ a ∈ A, parityVec (value x a)

def blockValues (W x : ℕ) : Finset ℕ := (offsets W).image (value x)

def oldValues {s : ℕ} (W : ℕ) (old : Fin s → ℕ) : Finset ℕ := univ.biUnion (fun j ↦ blockValues W (old j))

def Admissible (W x : ℕ) (A : Finset ℤ) : Prop :=
  Even A.card ∧ A ⊆ offsets W ∧ vector x A ≠ 0

def Witness {r s : ℕ} (W : ℕ) (old : Fin s → ℕ) (n : Fin r → ℕ) (A : Fin r → Finset ℤ) : Prop :=
  (∀ i, Admissible W (n i) (A i)) ∧ (∑ i, vector (n i) (A i)) ∈ oldSpace (oldValues W old)

def lists {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ ∃ A, Witness W old n A

def shortLists {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) (m : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (lists G W old).filter fun n ↦ ∃ A, Witness W old n A ∧ ∀ i, (A i).card ≤ m

theorem mem_lists {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) (n : Fin r → ℕ) :
    n ∈ lists G W old ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ ∃ A, Witness W old n A := by
  classical
  simp only [lists, mem_filter, Fintype.mem_piFinset]

theorem admissible_nonempty (W x : ℕ) (A : Finset ℤ) (hA : Admissible W x A) : A.Nonempty := by
  by_contra hnot
  have hz := not_nonempty_iff_eq_empty.mp hnot
  have hne := hA.2.2
  rw [hz, vector, sum_empty] at hne
  exact hne rfl

theorem vector_eq_product (W x : ℕ) (A : Finset ℤ) (hx : W < x) (hA : A ⊆ offsets W) :
    vector x A = parityVec (PaperP1.SplitOffsetProducts.product A x) := by
  have hp := PaperP1.SplitOffsetProducts.product_pos A x W hx ((subset_offsets W A).mp hA)
  have hf : ∀ a ∈ A, value x a ≠ 0 := prod_ne_zero_iff.mp hp.ne'
  exact (parityVec_prod A (value x) hf).symm

theorem oldValues_card {s : ℕ} (W : ℕ) (old : Fin s → ℕ) : (oldValues W old).card ≤ s * (2 * W + 1) := by
  calc
    _ ≤ ∑ j : Fin s, (blockValues W (old j)).card := card_biUnion_le
    _ ≤ ∑ _j : Fin s, (2 * W + 1) := by
      apply sum_le_sum
      intro j _
      have hc : (blockValues W (old j)).card ≤ (offsets W).card := card_image_le
      exact hc.trans_eq (offsets_card W)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem mem_oldValues {s : ℕ} (W : ℕ) (old : Fin s → ℕ) (v : ℕ) :
    v ∈ oldValues W old ↔ ∃ j : Fin s, ∃ a ∈ offsets W, value (old j) a = v := by
  simp only [oldValues, blockValues, mem_biUnion, mem_univ, true_and, mem_image]

theorem oldValues_cons {s : ℕ} (W x : ℕ) (old : Fin s → ℕ) :
    oldValues W (Fin.cons x old) = blockValues W x ∪ oldValues W old := by
  ext v
  simp only [mem_oldValues, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ, mem_union,
    blockValues, mem_image]

theorem vector_mem_oldSpace (O : Finset ℕ) (x : ℕ) (A : Finset ℤ)
    (hA : ∀ a ∈ A, value x a ∈ O) : vector x A ∈ oldSpace O := by
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.subset_span ⟨value x a, hA a ha, rfl⟩

theorem oldSpace_mono {O P : Finset ℕ} (hOP : O ⊆ P) : oldSpace O ≤ oldSpace P :=
  PaperP1.FiniteSetValueSpan.span_mono parityVec hOP

theorem witness_remove {r s : ℕ} (W : ℕ) (old : Fin s → ℕ) (n : Fin (r + 1) → ℕ)
    (A : Fin (r + 1) → Finset ℤ) (i : Fin (r + 1)) (hA : Witness W old n A) :
    Witness W (Fin.cons (n i) old) (i.removeNth n) (i.removeNth A) := by
  have hmono : oldSpace (oldValues W old) ≤ oldSpace (oldValues W (Fin.cons (n i) old)) := by
    apply oldSpace_mono
    rw [oldValues_cons]
    exact subset_union_right
  have hpivot : vector (n i) (A i) ∈ oldSpace (oldValues W (Fin.cons (n i) old)) := by
    apply vector_mem_oldSpace
    intro a ha
    rw [oldValues_cons]
    exact mem_union_left _ (mem_image.mpr ⟨a, (hA.1 i).2.1 ha, rfl⟩)
  have htotal := hmono hA.2
  have hsplit := Fin.add_sum_removeNth i (fun j ↦ vector (n j) (A j))
  have hrest : (∑ j : Fin r, vector (i.removeNth n j) (i.removeNth A j)) =
      (∑ j, vector (n j) (A j)) - vector (n i) (A i) := by
    rw [← hsplit]
    abel
  refine ⟨fun j ↦ hA.1 (i.succAbove j), ?_⟩
  rw [hrest]
  exact Submodule.sub_mem _ htotal hpivot

theorem lists_remove {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (n : Fin (r + 1) → ℕ) (i : Fin (r + 1)) (hn : n ∈ lists G W old) :
    i.removeNth n ∈ lists G W (Fin.cons (n i) old) := by
  obtain ⟨hG, hinj, A, hA⟩ := (mem_lists G W old n).mp hn
  apply (mem_lists G W _ _).mpr
  refine ⟨fun j ↦ hG (i.succAbove j), ?_, i.removeNth A, witness_remove W old n A i hA⟩
  have hi : Function.Injective i.succAbove := Fin.succAbove_right_injective
  exact hinj.comp hi

theorem lists_remove_pair {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (n : Fin (r + 2) → ℕ) (i : Fin (r + 2)) (j : Fin (r + 1)) (hn : n ∈ lists G W old) :
    j.removeNth (i.removeNth n) ∈ lists G W (Fin.cons (n (i.succAbove j)) (Fin.cons (n i) old)) :=
  lists_remove G W (Fin.cons (n i) old) (i.removeNth n) j (lists_remove G W old n i hn)

theorem one_fibre_count {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 1)) (x : ℕ) :
    ((lists (r := r + 1) G W old).filter fun n ↦ n i = x).card ≤
      (lists (r := r) G W (Fin.cons x old)).card := by
  classical
  apply PaperP1.FinTupleErasure.fixed_coordinate_count
  intro n hn hnx
  simpa only [hnx] using lists_remove G W old n i hn

theorem pair_fibre_count {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 2)) (j : Fin (r + 1)) (x y : ℕ) :
    ((lists (r := r + 2) G W old).filter fun n ↦ n i = x ∧ n (i.succAbove j) = y).card ≤
      (lists (r := r) G W (Fin.cons y (Fin.cons x old))).card := by
  classical
  apply PaperP1.FinTupleErasure.fixed_pair_count
  intro n hn hnx hny
  simpa only [hnx, hny] using lists_remove_pair G W old n i j hn

theorem zero_card {s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ) :
    (lists (r := 0) G W old).card ≤ 1 := by
  apply card_le_one.mpr
  intro n _ m _
  exact Subsingleton.elim n m

end PaperP1.ProjectedWindowLists
