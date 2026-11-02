module

public import PaperP1.Combinatorics.ReplicaTupleIndex
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring

/-! # Positive replica weight bounds preserve the exact first-tuple weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaWeightedCover

open Finset PaperP1.ReplicaTupleIndex

local instance replicaWeightedCoverDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def seedWeight {r : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) (x : Fin r → ℕ) : ℝ :=
  if x ∈ A then w x else 0

theorem seedWeight_nonneg {r : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (hw : ∀ x ∈ A, 0 ≤ w x) (x : Fin r → ℕ) : 0 ≤ seedWeight A w x := by
  unfold seedWeight
  split_ifs with hx
  · exact hw x hx
  · exact le_rfl

theorem seedWeight_mem {r : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    {x : Fin r → ℕ} (hx : x ∈ A) : seedWeight A w x = w x := by
  simp only [seedWeight, hx, ite_true]

theorem product_weight {r q : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (W : ℝ) (hw : ∀ x ∈ A, 0 ≤ w x) (hW : ∀ x ∈ A, w x ≤ W) (t : Fin (q + 1) → A) :
    (∏ j, w (t j).val) ≤ W ^ q * w (t 0).val := by
  rw [Fin.prod_univ_succ]
  have htail : (∏ j : Fin q, w (t j.succ).val) ≤ W ^ q := by
    calc
      _ ≤ ∏ _j : Fin q, W := prod_le_prod₀ (fun j _ ↦ hw _ (t j.succ).property)
        (fun j _ ↦ hW _ (t j.succ).property)
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left htail (hw _ (t 0).property)).trans_eq (mul_comm _ _)

theorem seed_sum {r : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (q : ℕ) (F : (Fin (r + q * r) → ℕ) → ℝ) :
    (∑ t : Fin (q + 1) → A, w (t 0).val * F (flatten (fun j ↦ (t j).val))) =
      ∑ y ∈ family A q, seedWeight A w (TupleExtensions.initial (q * r) y) * F y := by
  calc
    _ = ∑ t : Fin (q + 1) → A,
        seedWeight A w (TupleExtensions.initial (q * r) (flatten (fun j ↦ (t j).val))) *
          F (flatten (fun j ↦ (t j).val)) := by
      apply sum_congr rfl
      intro t _
      rw [initial_flatten, seedWeight_mem A w (t 0).property]
    _ = _ := by
      simpa only [family] using (sum_image
        (s := (univ : Finset (Fin (q + 1) → A)))
        (f := fun y ↦ seedWeight A w (TupleExtensions.initial (q * r) y) * F y)
        (subtype_flatten_injective A q).injOn).symm

theorem weighted_cover {r q : ℕ} (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (W : ℝ) (hw : ∀ x ∈ A, 0 ≤ w x) (hW : ∀ x ∈ A, w x ≤ W)
    (F : (Fin (r + q * r) → ℕ) → ℝ) (hF : ∀ y, 0 ≤ F y) :
    (∑ t : Fin (q + 1) → A, (∏ j, w (t j).val) * F (flatten (fun j ↦ (t j).val))) ≤
      W ^ q * ∑ y ∈ family A q, seedWeight A w (TupleExtensions.initial (q * r) y) * F y := by
  calc
    _ ≤ ∑ t : Fin (q + 1) → A, (W ^ q * w (t 0).val) * F (flatten (fun j ↦ (t j).val)) :=
      sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_right (product_weight A w W hw hW t) (hF _)
    _ = W ^ q * ∑ t : Fin (q + 1) → A, w (t 0).val * F (flatten (fun j ↦ (t j).val)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    _ = _ := congrArg (fun v : ℝ ↦ W ^ q * v) (seed_sum A w q F)

end PaperP1.ReplicaWeightedCover
