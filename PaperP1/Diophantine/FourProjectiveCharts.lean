module

public import PaperP1.Diophantine.BiformPointCoordinates

/-! # Four actual affine charts without discarding projective boundary points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourProjectiveCharts

open Finset PaperP1.BiformPointCoordinates PaperP1.UnimodularBinaryCoordinates

def matrix (flip : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if flip then !![0, 1; 1, 0] else 1

theorem matrix_squared (flip : Bool) : matrix flip * matrix flip = 1 := by
  cases flip with
  | false => simp [matrix]
  | true =>
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem matrix_height (flip : Bool) (i j : Fin 2) : (matrix flip i j).natAbs ≤ 1 := by
  cases flip <;> fin_cases i <;> fin_cases j <;> norm_num [matrix, Matrix.one_apply]

theorem last_coordinate (flip : Bool) (z : Fin 2 → ℤ) :
    (matrix flip).mulVec z 1 = if flip then z 0 else z 1 := by
  cases flip <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem first_coordinate (flip : Bool) (z : Fin 2 → ℤ) :
    (matrix flip).mulVec z 0 = if flip then z 1 else z 0 := by
  cases flip <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem selected_last_nonzero (z : Fin 2 → ℤ) (hz : z ≠ 0) :
    (matrix (decide (z 1 = 0))).mulVec z 1 ≠ 0 := by
  rw [last_coordinate]
  by_cases h : z 1 = 0
  · have h0 : z 0 ≠ 0 := by
      intro h0
      apply hz
      funext i
      fin_cases i <;> simp_all
    simpa only [show decide (z 1 = 0) = true by simp [h], Bool.true_eq, ite_true] using h0
  · simpa only [show decide (z 1 = 0) = false by simp [h], Bool.false_eq_true, ite_false] using h

def index (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : Bool × Bool :=
  (decide (p.1 1 = 0), decide (p.2 1 = 0))

def part (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) := S.filter (fun p ↦ index p = c)

def population (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) := (part c S).image (move (matrix c.1) (matrix c.2))

theorem population_card (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    (population c S).card = (part c S).card :=
  BiformPointCoordinates.population_card _ _ _ _ (matrix_squared c.1) (matrix_squared c.2) _

theorem finite_partition (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    S.card = ∑ c : Bool × Bool, (population c S).card := by
  simp_rw [population_card]
  exact card_eq_sum_card_fiberwise (fun _ _ ↦ mem_univ _)

theorem population_denominators (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∀ q ∈ population c S, q.1 1 ≠ 0 ∧ q.2 1 ≠ 0 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  obtain ⟨hp, hc⟩ := mem_filter.mp hp
  rw [← hc]
  exact ⟨selected_last_nonzero p.1 (hS p hp).1, selected_last_nonzero p.2 (hS p hp).2⟩

theorem population_primitive (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hS : ∀ p ∈ S, (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs) :
    ∀ q ∈ population c S,
      (q.1 0).natAbs.Coprime (q.1 1).natAbs ∧ (q.2 0).natAbs.Coprime (q.2 1).natAbs := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  exact move_primitive _ _ _ _ (matrix_squared c.1) (matrix_squared c.2) p (hS p (mem_filter.mp hp).1)

theorem population_height (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (L T : ℕ)
    (hS : ∀ p ∈ S, (∀ i, |p.1 i| ≤ (L : ℤ)) ∧ ∀ i, |p.2 i| ≤ (T : ℤ)) :
    ∀ q ∈ population c S, (∀ i, |q.1 i| ≤ (L : ℤ)) ∧ ∀ i, |q.2 i| ≤ (T : ℤ) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  have h := hS p (mem_filter.mp hp).1
  constructor
  · intro i
    fin_cases i
    · change |(matrix c.1).mulVec p.1 0| ≤ (L : ℤ)
      rw [first_coordinate]
      split_ifs <;> exact h.1 _
    · change |(matrix c.1).mulVec p.1 1| ≤ (L : ℤ)
      rw [last_coordinate]
      split_ifs <;> exact h.1 _
  · intro i
    fin_cases i
    · change |(matrix c.2).mulVec p.2 0| ≤ (T : ℤ)
      rw [first_coordinate]
      split_ifs <;> exact h.2 _
    · change |(matrix c.2).mulVec p.2 1| ≤ (T : ℤ)
      rw [last_coordinate]
      split_ifs <;> exact h.2 _

end PaperP1.FourProjectiveCharts
