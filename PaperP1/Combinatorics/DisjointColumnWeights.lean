module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

/-! # Actual column weights on disjoint blocks and the one-third deletion cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointColumnWeights

open Finset

variable {V J P R : Type*} [AddCommMonoid R] [DecidableEq R]

def column (rows : Finset P) (blocks : J → Finset V) (a : V → P → R) (j : J) : Finset P :=
  rows.filter (fun p ↦ ∑ v ∈ blocks j, a v p ≠ 0)

theorem mem_column (rows : Finset P) (blocks : J → Finset V) (a : V → P → R) (j : J) (p : P) :
    p ∈ column rows blocks a j ↔ p ∈ rows ∧ ∑ v ∈ blocks j, a v p ≠ 0 := by
  classical
  exact mem_filter

omit [DecidableEq R] in
theorem nonzero_column_has_contributor (blocks : J → Finset V) (a : V → P → R) (j : J) (p : P)
    (h : ∑ v ∈ blocks j, a v p ≠ 0) : ∃ v ∈ blocks j, a v p ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  exact h (sum_eq_zero hn)

theorem row_count_le (Q : Finset J) (A : Finset V) (blocks : J → Finset V) (a : V → P → R)
    (hsub : ∀ j ∈ Q, blocks j ⊆ A)
    (hdisjoint : (↑Q : Set J).Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (p : P) :
    (Q.filter (fun j ↦ ∑ v ∈ blocks j, a v p ≠ 0)).card ≤ (A.filter (fun v ↦ a v p ≠ 0)).card := by
  classical
  let T := Q.filter (fun j ↦ ∑ v ∈ blocks j, a v p ≠ 0)
  have hex (j : T) : ∃ v ∈ blocks j.val, a v p ≠ 0 :=
    nonzero_column_has_contributor blocks a j.val p (mem_filter.mp j.property).2
  choose v hv hne using hex
  let f : T → (A.filter (fun v ↦ a v p ≠ 0)) :=
    fun j ↦ ⟨v j, mem_filter.mpr ⟨hsub j.val (mem_filter.mp j.property).1 (hv j), hne j⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hneq
    have hd := hdisjoint (mem_filter.mp i.property).1 (mem_filter.mp j.property).1 hneq
    have he : v i = v j := congrArg Subtype.val hij
    exact (disjoint_left.mp hd) (hv i) (he ▸ hv j)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem sum_weights_eq_rows (Q : Finset J) (rows : Finset P) (blocks : J → Finset V) (a : V → P → R) :
    ∑ j ∈ Q, (column rows blocks a j).card =
      ∑ p ∈ rows, (Q.filter (fun j ↦ ∑ v ∈ blocks j, a v p ≠ 0)).card := by
  classical
  simp only [column, card_eq_sum_ones, sum_filter]
  exact sum_comm

theorem sum_weights_le (Q : Finset J) (A : Finset V) (rows : Finset P) (blocks : J → Finset V)
    (a : V → P → R) (hsub : ∀ j ∈ Q, blocks j ⊆ A)
    (hdisjoint : (↑Q : Set J).Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) :
    ∑ j ∈ Q, (column rows blocks a j).card ≤ ∑ p ∈ rows, (A.filter (fun v ↦ a v p ≠ 0)).card := by
  rw [sum_weights_eq_rows]
  exact sum_le_sum (fun p _ ↦ row_count_le Q A blocks a hsub hdisjoint p)

def light (Q : Finset J) (w : J → ℕ) : Finset J := Q.filter (fun j ↦ w j ≤ 2)

def heavy (Q : Finset J) (w : J → ℕ) : Finset J := Q.filter (fun j ↦ 3 ≤ w j)

theorem light_weight_le_two (Q : Finset J) (w : J → ℕ) (j : J) (hj : j ∈ light Q w) : w j ≤ 2 :=
  (mem_filter.mp hj).2

theorem heavy_weight_budget (Q : Finset J) (w : J → ℕ) :
    3 * (heavy Q w).card ≤ ∑ j ∈ Q, w j := by
  classical
  calc
    _ = ∑ _j ∈ heavy Q w, 3 := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; omega
    _ ≤ ∑ j ∈ heavy Q w, w j := sum_le_sum (fun _ hj ↦ (mem_filter.mp hj).2)
    _ ≤ ∑ j ∈ Q, w j := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)

theorem light_add_heavy (Q : Finset J) (w : J → ℕ) : (light Q w).card + (heavy Q w).card = Q.card := by
  classical
  have he : heavy Q w = Q.filter (fun j ↦ ¬w j ≤ 2) := by
    apply filter_congr
    intro j _hj
    omega
  rw [he, light, card_filter_add_card_filter_not]

theorem retained_card_lower (Q : Finset J) (w : J → ℕ) :
    Q.card - (∑ j ∈ Q, w j) / 3 ≤ (light Q w).card := by
  have h := heavy_weight_budget Q w
  have hp := light_add_heavy Q w
  have hdiv : (heavy Q w).card ≤ (∑ j ∈ Q, w j) / 3 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  omega

theorem retained_card_real (Q : Finset J) (w : J → ℕ) :
    (Q.card : ℝ) - (∑ j ∈ Q, (w j : ℝ)) / 3 ≤ ((light Q w).card : ℝ) := by
  have hw : 3 * ((heavy Q w).card : ℝ) ≤ ∑ j ∈ Q, (w j : ℝ) := by
    exact_mod_cast heavy_weight_budget Q w
  have hp : ((light Q w).card : ℝ) + (heavy Q w).card = Q.card := by
    exact_mod_cast light_add_heavy Q w
  linarith

end PaperP1.DisjointColumnWeights
