module

public import PaperP1.Arithmetic.ProjectedWindowLists

/-! # Actual coordinate populations reduce to actual fewer-target populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedWindowCounts

open Finset PaperP1.ProjectedWindowLists

theorem coordinate_sum {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 1)) (P : Finset ℕ) :
    ((lists (r := r + 1) G W old).filter fun n ↦ n i ∈ P).card ≤
      ∑ x ∈ P, (lists (r := r) G W (Fin.cons x old)).card := by
  classical
  let F := fun x ↦ (lists (r := r + 1) G W old).filter fun n ↦ n i = x
  have hcover : ((lists (r := r + 1) G W old).filter fun n ↦ n i ∈ P) ⊆ P.biUnion F := by
    intro n hn
    obtain ⟨hnL, hni⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨n i, hni, mem_filter.mpr ⟨hnL, rfl⟩⟩
  exact (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum fun x _ ↦ one_fibre_count G W old i x))

theorem coordinate_bound {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 1)) (P : Finset ℕ) (B : ℝ)
    (hB : ∀ x ∈ P, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤ B) :
    (((lists (r := r + 1) G W old).filter fun n ↦ n i ∈ P).card : ℝ) ≤ (P.card : ℝ) * B := by
  calc
    _ ≤ ((∑ x ∈ P, (lists (r := r) G W (Fin.cons x old)).card : ℕ) : ℝ) := by
      exact_mod_cast coordinate_sum G W old i P
    _ = ∑ x ∈ P, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _x ∈ P, B := sum_le_sum hB
    _ = _ := by simp

theorem any_coordinate_bound {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (P : Finset ℕ) (B : ℝ)
    (hB : ∀ x ∈ P, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤ B) :
    (((lists (r := r + 1) G W old).filter fun n ↦ ∃ i, n i ∈ P).card : ℝ) ≤
      (r + 1 : ℝ) * ((P.card : ℝ) * B) := by
  classical
  let S := (lists (r := r + 1) G W old).filter fun n ↦ ∃ i, n i ∈ P
  let F := fun i ↦ (lists (r := r + 1) G W old).filter fun n ↦ n i ∈ P
  have hcover : ∀ n ∈ S, ∃ i ∈ (univ : Finset (Fin (r + 1))), n ∈ F i := by
    intro n hn
    obtain ⟨hnL, i, hi⟩ := mem_filter.mp hn
    exact ⟨i, mem_univ i, mem_filter.mpr ⟨hnL, hi⟩⟩
  have hF : ∀ i ∈ (univ : Finset (Fin (r + 1))), ((F i).card : ℝ) ≤ (P.card : ℝ) * B :=
    fun i _ ↦ coordinate_bound G W old i P B hB
  have hc := PaperP1.FiniteCoverCount.cardinal_le S (univ : Finset (Fin (r + 1))) F _ hcover hF
  simpa only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hc

theorem pair_sum {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 2)) (j : Fin (r + 1)) (P : Finset (ℕ × ℕ)) :
    ((lists (r := r + 2) G W old).filter fun n ↦ (n i, n (i.succAbove j)) ∈ P).card ≤
      ∑ p ∈ P, (lists (r := r) G W (Fin.cons p.2 (Fin.cons p.1 old))).card := by
  classical
  let F := fun p : ℕ × ℕ ↦ (lists (r := r + 2) G W old).filter fun n ↦ n i = p.1 ∧ n (i.succAbove j) = p.2
  have hcover : ((lists (r := r + 2) G W old).filter fun n ↦ (n i, n (i.succAbove j)) ∈ P) ⊆ P.biUnion F := by
    intro n hn
    obtain ⟨hnL, hni⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨(n i, n (i.succAbove j)), hni, mem_filter.mpr ⟨hnL, rfl, rfl⟩⟩
  exact (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum fun p _ ↦ pair_fibre_count G W old i j p.1 p.2))

theorem pair_bound {r s : ℕ} (G : Finset ℕ) (W : ℕ) (old : Fin s → ℕ)
    (i : Fin (r + 2)) (j : Fin (r + 1)) (P : Finset (ℕ × ℕ)) (B : ℝ)
    (hB : ∀ p ∈ P, ((lists (r := r) G W (Fin.cons p.2 (Fin.cons p.1 old))).card : ℝ) ≤ B) :
    (((lists (r := r + 2) G W old).filter fun n ↦ (n i, n (i.succAbove j)) ∈ P).card : ℝ) ≤
      (P.card : ℝ) * B := by
  calc
    _ ≤ ((∑ p ∈ P, (lists (r := r) G W (Fin.cons p.2 (Fin.cons p.1 old))).card : ℕ) : ℝ) := by
      exact_mod_cast pair_sum G W old i j P
    _ = ∑ p ∈ P, ((lists (r := r) G W (Fin.cons p.2 (Fin.cons p.1 old))).card : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _p ∈ P, B := sum_le_sum hB
    _ = _ := by simp

end PaperP1.ProjectedWindowCounts
