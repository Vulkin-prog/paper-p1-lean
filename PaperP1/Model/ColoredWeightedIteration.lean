module

public import PaperP1.Model.ColoredTupleMass
public import PaperP1.Combinatorics.TupleExtensions
public import Mathlib.Tactic.Ring

/-! # Colored mass propagation retains arbitrary nonnegative seed weights exactly -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredWeightedIteration

open Finset PaperP1.Arithmetic PaperP1.ColoredTupleMass

variable {κ : Type*} [Fintype κ]

theorem iterate {s r M Y L : ℕ} (G : Finset ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂) (B : ℝ)
    (hs : 1 ≤ s) (hB : 0 ≤ B)
    (hstep : ∀ q : ℕ, 1 ≤ q → q ≤ r → ∀ x : Fin q → ℕ, (∀ i, x i ∈ G) →
      (∑ z ∈ G, joint M Y L χ c (append x z)) ≤ B * joint M Y L χ c x)
    (F : Finset (Fin s → ℕ)) (hF : ∀ x ∈ F, ∀ i, x i ∈ G)
    (a : (Fin s → ℕ) → ℝ) (ha : ∀ x, 0 ≤ a x) (k : ℕ) (hsize : s + k ≤ r) :
    (∑ y ∈ TupleExtensions.more G F k, a (TupleExtensions.initial k y) * joint M Y L χ c y) ≤
      B ^ k * ∑ x ∈ F, a x * joint M Y L χ c x := by
  induction k with
  | zero =>
      simp only [TupleExtensions.more, TupleExtensions.initial, pow_zero, one_mul]
      exact @Preorder.le_refl ℝ Real.partialOrder.toPreorder _
  | succ k ih =>
    have hprevious := ih (by omega)
    have hcoordinates := TupleExtensions.more_coordinates G F hF k
    calc
      _ = ∑ x ∈ TupleExtensions.more G F k, a (TupleExtensions.initial k x) *
          ∑ z ∈ G, joint M Y L χ c (append x z) := by
        have hsum := TupleExtensions.step_sum G (TupleExtensions.more G F k)
          (fun y ↦ a (TupleExtensions.initial (k + 1) y) * joint M Y L χ c y)
        calc
          _ = _ := hsum
          _ = _ := by
            simp only [TupleExtensions.initial, TupleExtensions.append, Fin.init_snoc]
            simp_rw [mul_sum]
      _ ≤ ∑ x ∈ TupleExtensions.more G F k,
          a (TupleExtensions.initial k x) * (B * joint M Y L χ c x) := by
        apply sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left
          (hstep (s + k) (by omega) (by omega) x (hcoordinates x hx)) (ha _)
      _ = B * ∑ x ∈ TupleExtensions.more G F k,
          a (TupleExtensions.initial k x) * joint M Y L χ c x := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ B * (B ^ k * ∑ x ∈ F, a x * joint M Y L χ c x) :=
        mul_le_mul_of_nonneg_left hprevious hB
      _ = _ := by rw [pow_succ]; ring

end PaperP1.ColoredWeightedIteration
