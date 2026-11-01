module

public import PaperP1.Asymptotics.PositionedMassPropagation
public import PaperP1.Asymptotics.IrregularSeedMass
public import PaperP1.Arithmetic.ExactContactSeeds

/-! # Actual propagated local-defect and exact-contact masses at every seed position -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionedSeedBounds

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.RegularStarts

theorem defects (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ TuplePositions.allPositions (Ico N (2 * N)) (SingletonSeedMass.seeds (irregularStarts N L)) k,
          joint L c x) ≤
          (((1 + k).factorial : ℝ) * (2 * (2 : ℝ) ^ C)) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, hNP⟩ := PositionedMassPropagation.all_positions 1 (by omega) k C (ε / 2) (by positivity)
  obtain ⟨NS, hNS⟩ := IrregularSeedMass.seed_family C (ε / 2) (by positivity)
  refine ⟨max NP (max NS 1), ?_⟩
  intro N hN L hL hband c
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprop := hNP N (by omega) L hband c _ (IrregularSeedMass.seed_coordinates N L)
  have hseed := hNS N (by omega) L hL hband c
  calc
    _ ≤ _ := hprop
    _ ≤ ((1 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 2) * ((2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hseed (by positivity)
    _ = (((1 + k).factorial : ℝ) * (2 * (2 : ℝ) ^ C)) *
        ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-1 + ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hNr, show ε / 2 + (-1 + ε / 2) = -1 + ε by ring]

theorem contacts (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ TuplePositions.allPositions (Ico N (2 * N)) (ExactContactSeeds.seeds N L) k, joint L c x) ≤
          (((2 + k).factorial : ℝ) * ((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, hNP⟩ := PositionedMassPropagation.all_positions 2 (by omega) k C (ε / 2) (by positivity)
  obtain ⟨NS, hNS⟩ := ExactContactSeeds.seed_mass C (ε / 2) (by positivity)
  refine ⟨max NP (max NS 1), ?_⟩
  intro N hN L hband c
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprop := hNP N (by omega) L hband c _ (ExactContactSeeds.seed_coordinates N L)
  have hseed := hNS N (by omega) L hband c
  calc
    _ ≤ _ := hprop
    _ ≤ ((2 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 2) * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hseed (by positivity)
    _ = (((2 + k).factorial : ℝ) * ((2 : ℝ) ^ C) ^ 2) *
        ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-1 + ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hNr, show ε / 2 + (-1 + ε / 2) = -1 + ε by ring]

end PaperP1.PositionedSeedBounds
