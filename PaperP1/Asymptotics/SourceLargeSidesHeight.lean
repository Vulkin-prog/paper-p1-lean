module

public import PaperP1.Asymptotics.ConstructedClusterCurveData

/-! # Both actual large lattice sides have one fixed polynomial height bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceLargeSidesHeight

open PaperP1.DeterminantSourceBox

theorem upper_to_fifth_power (N : ℕ) (hN : 1 ≤ N) (R L : ℝ) (hR : 0 ≤ R)
    (hRN : 6 * R ≤ N) (hL : L ≤ 2 * R * (((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) + 1)) :
    L ≤ (N : ℝ) ^ 5 := by
  have h4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hN)
  have hp : ((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) = 2 * (N : ℝ) ^ 4 := by push_cast; ring
  rw [hp] at hL
  calc
    _ ≤ 2 * R * (2 * (N : ℝ) ^ 4 + 1) := hL
    _ ≤ 6 * R * (N : ℝ) ^ 4 := by nlinarith only [mul_nonneg hR (sub_nonneg.mpr h4)]
    _ ≤ (N : ℝ) * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hRN (by positivity)
    _ = _ := by ring

theorem uniform_height (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ κ₀ κ₁ M k : ℕ,
      ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
        L₀ ≤ (N : ℝ) ^ 5 ∧ T₀ ≤ (N : ℝ) ^ 5 := by
  let Q := ⌈max 12 (12 * (49 + 16 / ρ))⌉₊ + 1
  have hQ : max 12 (12 * (49 + 16 / ρ)) ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil (max 12 (12 * (49 + 16 / ρ)))
    dsimp [Q]
    push_cast
    linarith
  refine ⟨max 1 Q, ?_⟩
  intro N hN C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU
  have hNR : (Q : ℝ) ≤ N := by exact_mod_cast (show Q ≤ N by omega)
  have h12 : (12 : ℝ) ≤ N := (le_max_left _ _).trans (hQ.trans hNR)
  have hvertical : 6 * (2 * (49 + 16 / ρ)) ≤ (N : ℝ) := by
    have hh := (le_max_right _ _).trans (hQ.trans hNR)
    nlinarith only [hh]
  constructor
  · apply upper_to_fifth_power N (by omega) 2 L₀ (by norm_num) (by nlinarith only [h12])
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hD.large_upper
  · exact upper_to_fifth_power N (by omega) (2 * (49 + 16 / ρ)) T₀
      (by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hρ.le; linarith) hvertical hU.large_upper

end PaperP1.SourceLargeSidesHeight
