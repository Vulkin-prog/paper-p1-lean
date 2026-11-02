module

public import PaperP1.Combinatorics.GraphStarWeights
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Actual unordered close pairs and a heterogeneous independent-weight budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClosePairs

open Finset

def pairs (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard 2).filter (fun e ↦ ∃ x ∈ e, ∃ y ∈ e, x < y ∧ y ≤ x + L)

theorem subset (G : Finset ℕ) (L : ℕ) : pairs G L ⊆ G.powersetCard 2 := by
  classical
  exact filter_subset _ _

theorem data (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (he : e ∈ pairs G L) :
    ∃ x y : ℕ, x ∈ G ∧ y ∈ G ∧ x < y ∧ y ≤ x + L ∧ e = {x, y} := by
  classical
  obtain ⟨he, x, hxe, y, hye, hxy, hyL⟩ := mem_filter.mp he
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
  have hpair : ({x, y} : Finset ℕ) = e := eq_of_subset_of_card_le
    (by intro z hz; simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption)
    (by rw [hecard]; simp [ne_of_lt hxy])
  exact ⟨x, y, heG hxe, heG hye, hxy, hyL, hpair.symm⟩

theorem forward_cover (G : Finset ℕ) (L : ℕ) :
    pairs G L ⊆ G.biUnion (fun x ↦ (G ∩ Icc (x + 1) (x + L)).image (fun y ↦ {x, y})) := by
  classical
  intro e he
  obtain ⟨x, y, hx, hy, hxy, hyL, rfl⟩ := data G L e he
  exact mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨y,
    mem_inter.mpr ⟨hy, mem_Icc.mpr ⟨by omega, hyL⟩⟩, rfl⟩⟩

set_option maxHeartbeats 1000000 in
theorem independent_weight_bound (G : Finset ℕ) (L : ℕ) (p : ℕ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (P : ℝ) (hP : 0 ≤ P) (hcap : ∀ x ∈ G, p x ≤ P) :
    (∑ e ∈ pairs G L, ∏ x ∈ e, p x) ≤ (L : ℝ) * P * ∑ x ∈ G, p x := by
  classical
  let A : ℕ → Finset (Finset ℕ) := fun x ↦
    (G ∩ Icc (x + 1) (x + L)).image (fun y ↦ {x, y})
  have hrow (x : ℕ) : (∑ y ∈ G ∩ Icc (x + 1) (x + L), p y) ≤ (L : ℝ) * P := by
    have hcard : ((G ∩ Icc (x + 1) (x + L)).card : ℝ) ≤ L := by
      have h := card_le_card (inter_subset_right : G ∩ Icc (x + 1) (x + L) ⊆ Icc (x + 1) (x + L))
      have hc : (Icc (x + 1) (x + L)).card = L := by rw [Nat.card_Icc]; omega
      exact_mod_cast h.trans_eq hc
    calc
      _ ≤ ∑ _y ∈ G ∩ Icc (x + 1) (x + L), P := sum_le_sum fun y hy ↦ hcap y (mem_inter.mp hy).1
      _ = ((G ∩ Icc (x + 1) (x + L)).card : ℝ) * P := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hP
  calc
    _ ≤ ∑ e ∈ G.biUnion A, ∏ x ∈ e, p x :=
      sum_le_sum_of_subset_of_nonneg (f := fun e : Finset ℕ ↦ ∏ x ∈ e, p x)
        (forward_cover G L) (fun e _ _ ↦ prod_nonneg fun x _ ↦ hp x)
    _ ≤ ∑ x ∈ G, ∑ e ∈ A x, ∏ z ∈ e, p z :=
      GraphStarWeights.sum_biUnion_le_nonneg G A
        (fun e : Finset ℕ ↦ ∏ z ∈ e, p z) (fun e ↦ prod_nonneg fun z _ ↦ hp z)
    _ ≤ ∑ x ∈ G, p x * ((L : ℝ) * P) := by
      apply sum_le_sum
      intro x _
      dsimp only [A]
      calc
        _ ≤ ∑ y ∈ G ∩ Icc (x + 1) (x + L), ∏ z ∈ ({x, y} : Finset ℕ), p z :=
          sum_image_le_of_nonneg (s := G ∩ Icc (x + 1) (x + L))
            (g := fun y ↦ ({x, y} : Finset ℕ)) (f := fun e : Finset ℕ ↦ ∏ z ∈ e, p z)
            (fun e _ ↦ prod_nonneg fun z _ ↦ hp z)
        _ = p x * ∑ y ∈ G ∩ Icc (x + 1) (x + L), p y := by
          rw [mul_sum]
          apply sum_congr rfl
          intro y hy
          have hxy : x ≠ y := by have h := (mem_Icc.mp (mem_inter.mp hy).2).1; omega
          exact prod_pair hxy
        _ ≤ _ := mul_le_mul_of_nonneg_left (hrow x) (hp x)
    _ = _ := by rw [← sum_mul]; ring

end PaperP1.ClosePairs
