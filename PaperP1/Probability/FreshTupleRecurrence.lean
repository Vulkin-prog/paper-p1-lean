module

public import PaperP1.Probability.BranchingTuples
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Exact fresh-site recurrence for ordered distinct-tuple masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FreshTupleRecurrence

open Finset PaperP1.Probability PaperP1.BranchingTuples

variable {ι : Type*} [DecidableEq ι]

def consTuple {G : Finset ι} {r : ℕ} (z : G) (t : OrderedTuple G r)
    (hz : z.val ∉ tupleValues t) : OrderedTuple G (r + 1) where
  toFun := Fin.cons z t
  inj' := by
    intro i j
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · intro _; rfl
      · intro hij
        have hb : (t b).val = z.val := congrArg Subtype.val hij.symm
        exact False.elim (hz ((mem_tupleValues t z.val).mpr ⟨b, hb⟩))
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · intro hij
        have ha : (t a).val = z.val := congrArg Subtype.val hij
        exact False.elim (hz ((mem_tupleValues t z.val).mpr ⟨a, ha⟩))
      · intro hij
        exact congrArg Fin.succ (t.injective hij)

theorem encoding_image (G : Finset ι) (r : ℕ) :
    (univ.image fun t : OrderedTuple G (r + 1) ↦ (t 0, eraseTuple t 0)) =
      (univ : Finset (G × OrderedTuple G r)).filter (fun v ↦ v.1.val ∉ tupleValues v.2) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨t, _ht, rfl⟩ := mem_image.mp hv
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [tupleValues_erase]
    intro hz
    exact (mem_erase.mp hz).1 rfl
  · intro hv
    have hz := (mem_filter.mp hv).2
    let t := consTuple v.1 v.2 hz
    refine mem_image.mpr ⟨t, mem_univ _, ?_⟩
    apply Prod.ext
    · change (Fin.cons v.1 (fun j : Fin r ↦ v.2 j) : Fin (r + 1) → G) 0 = v.1
      exact Fin.cons_zero _ _
    · apply Function.Embedding.ext
      intro i
      change (Fin.cons v.1 (fun j : Fin r ↦ v.2 j) : Fin (r + 1) → G) ((0 : Fin (r + 1)).succAbove i) = v.2 i
      simp only [Fin.succAbove_zero, Fin.cons_succ]

theorem sum_succ_eq_fresh (G : Finset ι) (r : ℕ) (q : Finset ι → ℝ) :
    (∑ t : OrderedTuple G (r + 1), q (tupleValues t)) =
      ∑ t : OrderedTuple G r, ∑ z ∈ G \ tupleValues t, q (insert z (tupleValues t)) := by
  classical
  let enc : OrderedTuple G (r + 1) → G × OrderedTuple G r := fun t ↦ (t 0, eraseTuple t 0)
  calc
    _ = ∑ t : OrderedTuple G (r + 1), q (insert (t 0).val (tupleValues (eraseTuple t 0))) :=
      sum_congr rfl (fun t _ ↦ congrArg q (tupleValues_insert_erased t 0))
    _ = ∑ v ∈ univ.image enc, q (insert v.1.val (tupleValues v.2)) := by
      rw [sum_image (eraseTuple_encoding_injective (0 : Fin (r + 1))).injOn]
    _ = ∑ v : G × OrderedTuple G r,
        if v.1.val ∉ tupleValues v.2 then q (insert v.1.val (tupleValues v.2)) else 0 := by
      rw [show univ.image enc = _ from encoding_image G r, sum_filter]
    _ = _ := by
      rw [Fintype.sum_prod_type, sum_comm]
      apply sum_congr rfl
      intro t _
      dsimp only
      calc
        _ = ∑ z ∈ G, if z ∉ tupleValues t then q (insert z (tupleValues t)) else 0 :=
          sum_coe_sort G (fun z ↦ if z ∉ tupleValues t then q (insert z (tupleValues t)) else 0)
        _ = _ := by
          rw [← sum_filter]
          congr 1
          ext z
          simp only [mem_filter, mem_sdiff]

theorem sum_succ_lower (G : Finset ι) (r : ℕ) (q : Finset ι → ℝ) (M : ℝ)
    (hbudget : ∀ A : Finset ι, A ⊆ G → A.card = r →
      M * q A ≤ ∑ z ∈ G \ A, q (insert z A)) :
    M * (∑ t : OrderedTuple G r, q (tupleValues t)) ≤
      ∑ t : OrderedTuple G (r + 1), q (tupleValues t) := by
  rw [sum_succ_eq_fresh, mul_sum]
  exact sum_le_sum fun t _ ↦ hbudget (tupleValues t) (tupleValues_subset t) (tupleValues_card t)

end PaperP1.FreshTupleRecurrence
