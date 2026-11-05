module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The triangular budget for distinct degrees truncated at the matrix order

The high-degree remainder slots may all have the same truncated weight. The
actual distinct slot indices still force the full triangular total weight.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedEvaluationDegreeBudget

open Finset

theorem strictly_mono_index_le (n : ℕ) (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) : i.val ≤ f i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hnext := hf (show i.castSucc < i.succ by simp)
      change i.val ≤ f i.castSucc at ih
      change i.val + 1 ≤ f i.succ
      omega

theorem truncated_range_budget (n : ℕ) (f : Fin n → ℕ) (hf : Function.Injective f) :
    (∑ i ∈ range n, i) ≤ ∑ i, min (f i) (n - 1) := by
  classical
  let S := (univ : Finset (Fin n)).image f
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ hf, card_univ, Fintype.card_fin]
  let e : Fin n ↪o ℕ := S.orderEmbOfFin hcard
  have hsumf : (∑ i : Fin n, min (f i) (n - 1)) = ∑ v ∈ S, min v (n - 1) := by
    dsimp only [S]
    rw [Finset.sum_image (fun i _hi j _hj he ↦ hf he)]
  have hsume : (∑ i : Fin n, min (e i) (n - 1)) = ∑ v ∈ S, min v (n - 1) := by
    rw [← S.image_orderEmbOfFin_univ hcard, Finset.sum_image (fun i _hi j _hj he ↦ e.injective he)]
  calc
    _ = ∑ i : Fin n, i.val := (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n).symm
    _ ≤ ∑ i : Fin n, min (e i) (n - 1) := by
      apply sum_le_sum
      intro i _hi
      exact le_min (strictly_mono_index_le n e e.strictMono i) (by have := i.isLt; omega)
    _ = ∑ v ∈ S, min v (n - 1) := hsume
    _ = _ := hsumf.symm

theorem triangular_budget (n : ℕ) (f : Fin n → ℕ) (hf : Function.Injective f) :
    n * (n - 1) / 2 ≤ ∑ i, min (f i) (n - 1) := by
  simpa only [Finset.sum_range_id] using truncated_range_budget n f hf

end PaperP1.TruncatedEvaluationDegreeBudget
