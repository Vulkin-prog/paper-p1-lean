module

public import PaperP1.Analysis.DeterminantSevenTwelfthsCosts
public import PaperP1.Asymptotics.NonprimitiveSourceDeterminantCount

/-! # Apply the full determinant theorem to give the sharp interior source-box exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SevenTwelfthsSourceCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox PaperP1.IntegralSourceCoefficients
open PaperP1.DeterminantSignedBoxes

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      (N : ℝ) ≤ X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ T : ℝ, 0 ≤ T → X.U ≤ T → X.V ≤ T →
      ∀ S : Finset Quad, SignedPopulation X h S →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨Nf, hf⟩ := NonprimitiveSourceDeterminantCount.uniform_signed_count hHB hNG δ C ρ K A (ε / 2)
    hδ hC hρ hρ₁ hK hA (by positivity)
  obtain ⟨Nc, hc⟩ := DeterminantSevenTwelfthsCosts.uniform_complete_cost C (ε / 2) hC (by positivity)
  refine ⟨max 1 (max Nf Nc), ?_⟩
  intro N hN h hh hshift X coefs hb T hT hU hV S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hf N (by omega) h hh hshift X coefs hb S hS
  have hcost := hc N (by omega) ρ δ X T hT hU hV
  calc
    _ ≤ (N : ℝ) ^ (ε / 2) *
        min (Real.sqrt (X.D * X.E * Real.exp (DeterminantLogScale.logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (DeterminantLogScale.logShape N X.D X.E X.U X.V)) + X.U + X.V) := hcount
    _ ≤ (N : ℝ) ^ (ε / 2) * ((T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hn.le _)
    _ = _ := by
      calc
        _ = (T + (N : ℝ) ^ (7 / 12 : ℝ)) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

end PaperP1.SevenTwelfthsSourceCount
