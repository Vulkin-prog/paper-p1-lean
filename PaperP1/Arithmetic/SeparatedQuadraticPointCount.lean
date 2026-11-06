module

public import PaperP1.Arithmetic.QuadraticCharacterRootCount
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Exact finite-field character expansion for the literal separated square-root equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedQuadraticPointCount

open Finset QuadraticCharacterRootCount
open scoped Classical

variable {F ι : Type*} [Field F] [Fintype F] [Fintype ι]

def points (c : ι → F) (A B : ι → F → F) : Finset ((F × F) × (ι → F)) :=
  univ.filter (fun w ↦ ∀ i, w.2 i ^ 2 = c i * A i w.1.1 * B i w.1.2)

def characterSum (A : ι → F → F) (s : Finset ι) : ℤ :=
  ∑ x : F, quadraticChar F (∏ i ∈ s, A i x)

theorem mem_points (c : ι → F) (A B : ι → F → F) (w : (F × F) × (ι → F)) :
    w ∈ points c A B ↔ ∀ i, w.2 i ^ 2 = c i * A i w.1.1 * B i w.1.2 := by
  simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]

theorem fiber_cardinality (c : ι → F) (A B : ι → F → F) :
    (points c A B).card = ∑ x : F, ∑ y : F, (roots (fun i ↦ c i * A i x * B i y)).card := by
  let e : {w : (F × F) × (ι → F) // ∀ i, w.2 i ^ 2 = c i * A i w.1.1 * B i w.1.2} ≃
      Σ xy : F × F, {z : ι → F // ∀ i, z i ^ 2 = c i * A i xy.1 * B i xy.2} :=
    { toFun := fun w ↦ ⟨w.val.1, w.val.2, w.property⟩
      invFun := fun w ↦ ⟨(w.1, w.2.val), w.2.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc : (points c A B).card = Fintype.card {w : (F × F) × (ι → F) //
      ∀ i, w.2 i ^ 2 = c i * A i w.1.1 * B i w.1.2} := by
    symm
    exact Fintype.card_of_finset'
      (p := {w : (F × F) × (ι → F) | ∀ i, w.2 i ^ 2 = c i * A i w.1.1 * B i w.1.2})
      (points c A B) (fun w ↦ by
        simp only [points, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq])
  rw [hc, Fintype.card_congr e, Fintype.card_sigma, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  exact Fintype.card_of_finset' (p := {z : ι → F | ∀ i, z i ^ 2 = c i * A i x * B i y})
    (roots _) (fun z ↦ by simp only [roots, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq])

omit [Fintype ι] in
theorem subset_factorization (c : ι → F) (A B : ι → F → F) (s : Finset ι) (x y : F) :
    (∏ i ∈ s, quadraticChar F (c i * A i x * B i y)) =
      quadraticChar F (∏ i ∈ s, c i) *
        quadraticChar F (∏ i ∈ s, A i x) * quadraticChar F (∏ i ∈ s, B i y) := by
  simp only [map_mul, map_prod, prod_mul_distrib]

omit [Fintype ι] in
theorem subset_sum (c : ι → F) (A B : ι → F → F) (s : Finset ι) :
    (∑ x : F, ∑ y : F, ∏ i ∈ s, quadraticChar F (c i * A i x * B i y)) =
      quadraticChar F (∏ i ∈ s, c i) * characterSum A s * characterSum B s := by
  simp_rw [subset_factorization]
  simp only [characterSum, mul_sum, sum_mul, mul_assoc]
  exact sum_comm

theorem character_expansion (hodd : ringChar F ≠ 2) (c : ι → F) (A B : ι → F → F) :
    ((points c A B).card : ℤ) =
      ∑ s ∈ (univ : Finset ι).powerset,
        quadraticChar F (∏ i ∈ s, c i) * characterSum A s * characterSum B s := by
  rw [fiber_cardinality, Nat.cast_sum]
  simp_rw [Nat.cast_sum, QuadraticCharacterRootCount.cardinality hodd, prod_one_add]
  calc
    _ = ∑ x : F, ∑ s ∈ (univ : Finset ι).powerset,
        ∑ y : F, ∏ i ∈ s, quadraticChar F (c i * A i x * B i y) := by
      apply sum_congr rfl
      intro x _
      exact sum_comm
    _ = _ := ?_
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  exact subset_sum c A B s

omit [Fintype ι] in
theorem empty_character_sum (A : ι → F → F) : characterSum A ∅ = Fintype.card F := by
  simp [characterSum]

end PaperP1.SeparatedQuadraticPointCount
