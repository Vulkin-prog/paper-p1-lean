module

public import PaperP1.Probability.OrderedTuples
public import Mathlib.Tactic.Positivity

/-! # Positive extension budgets imply recurrences for actual distinct-tuple sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BranchingTuples

open Finset PaperP1.Probability

variable {ι : Type*} [DecidableEq ι]

theorem tupleValues_insert_erased {G : Finset ι} {r : ℕ} (t : OrderedTuple G (r + 1)) (i : Fin (r + 1)) :
    tupleValues t = insert (t i).val (tupleValues (eraseTuple t i)) := by
  rw [tupleValues_erase, insert_erase ((mem_tupleValues t (t i).val).mpr ⟨i, rfl⟩)]

theorem sum_tuple_succ_le (G : Finset ι) (r : ℕ) (q : Finset ι → ℝ) (hq : ∀ A, 0 ≤ q A)
    (M : ℝ) (hbudget : ∀ A : Finset ι, A ⊆ G → A.card = r → (∑ x ∈ G, q (insert x A)) ≤ M * q A) :
    (∑ t : OrderedTuple G (r + 1), q (tupleValues t)) ≤ M * ∑ t : OrderedTuple G r, q (tupleValues t) := by
  classical
  let i : Fin (r + 1) := 0
  let enc : OrderedTuple G (r + 1) → G × OrderedTuple G r := fun t ↦ (t i, eraseTuple t i)
  have hinj : Function.Injective enc := eraseTuple_encoding_injective i
  calc
    _ = ∑ t : OrderedTuple G (r + 1), q (insert (t i).val (tupleValues (eraseTuple t i))) :=
      sum_congr rfl (fun t _ ↦ congrArg q (tupleValues_insert_erased t i))
    _ = ∑ v ∈ univ.image enc, q (insert v.1.val (tupleValues v.2)) := by
      rw [sum_image hinj.injOn]
    _ ≤ ∑ v : G × OrderedTuple G r, q (insert v.1.val (tupleValues v.2)) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ hq _)
    _ = ∑ t : OrderedTuple G r, ∑ x ∈ G, q (insert x (tupleValues t)) := by
      rw [Fintype.sum_prod_type, sum_comm]
      apply sum_congr rfl
      intro t _
      exact sum_coe_sort G (fun x ↦ q (insert x (tupleValues t)))
    _ ≤ ∑ t : OrderedTuple G r, M * q (tupleValues t) :=
      sum_le_sum (fun t _ ↦ hbudget _ (tupleValues_subset t) (tupleValues_card t))
    _ = _ := (mul_sum _ _ _).symm

end PaperP1.BranchingTuples
