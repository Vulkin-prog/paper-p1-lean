module

public import PaperP1.Diophantine.FourProjectiveCharts

/-! # All four signed projective charts retain the actual real side bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourChartRealBounds

open Finset PaperP1.FourProjectiveCharts

theorem population_bounds (c : Bool × Bool) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (L T : ℝ)
    (hS : ∀ p ∈ S, (∀ i, |(p.1 i : ℝ)| ≤ L) ∧ ∀ i, |(p.2 i : ℝ)| ≤ T) :
    ∀ q ∈ population c S, (∀ i, |(q.1 i : ℝ)| ≤ L) ∧ ∀ i, |(q.2 i : ℝ)| ≤ T := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
  have h := hS p (mem_filter.mp hp).1
  constructor
  · intro i
    fin_cases i
    · change |((matrix c.1).mulVec p.1 0 : ℝ)| ≤ L
      rw [first_coordinate]
      split_ifs <;> exact h.1 _
    · change |((matrix c.1).mulVec p.1 1 : ℝ)| ≤ L
      rw [last_coordinate]
      split_ifs <;> exact h.1 _
  · intro i
    fin_cases i
    · change |((matrix c.2).mulVec p.2 0 : ℝ)| ≤ T
      rw [first_coordinate]
      split_ifs <;> exact h.2 _
    · change |((matrix c.2).mulVec p.2 1 : ℝ)| ≤ T
      rw [last_coordinate]
      split_ifs <;> exact h.2 _

end PaperP1.FourChartRealBounds
