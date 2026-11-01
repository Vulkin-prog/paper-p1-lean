module

public import PaperP1.Asymptotics.FixedOrderMassPropagation
public import PaperP1.Model.PrescribedTuplePositions

/-! # Actual seed mass propagation with all ordered seed positions included -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionedMassPropagation

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass

theorem all_positions (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TuplePositions.allPositions (Ico N (2 * N)) F k, joint L c y) ≤
          ((s + k).factorial : ℝ) * (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  obtain ⟨N₀, hN₀⟩ := FixedOrderMassPropagation.main_6_3_propagation s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband c F hF
  have hpositions := TuplePositions.mass_bound (Ico N (2 * N)) F k (joint L c)
    (joint_nonneg c) (PrescribedTuplePositions.joint_permute c)
  calc
    _ ≤ _ := hpositions
    _ ≤ ((s + k).factorial : ℝ) * ((N : ℝ) ^ ε * ∑ x ∈ F, joint L c x) :=
      mul_le_mul_of_nonneg_left (hN₀ N hN L hband c F hF) (Nat.cast_nonneg _)
    _ = _ := by ring

end PaperP1.PositionedMassPropagation
