module

public import PaperP1.Arithmetic.DeterminantPositiveOrientation

/-! # Literal integer coefficients and the source barrier used by the arithmetic local counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralSourceCoefficients

open PaperP1.DeterminantSourceBox PaperP1.DeterminantPositiveOrientation PaperP1.DeterminantSignedBoxes

structure IntegerCoefficients {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) where
  c₁ : ℕ
  c₂ : ℕ
  first_eq : X.c₁ = (c₁ : ℝ)
  second_eq : X.c₂ = (c₂ : ℝ)

theorem positive {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X) :
    1 ≤ d.c₁ ∧ 1 ≤ d.c₂ := by
  have h₁ : (1 : ℝ) ≤ d.c₁ := by simpa only [d.first_eq] using X.c₁_ge_one
  have h₂ : (1 : ℝ) ≤ d.c₂ := by simpa only [d.second_eq] using X.c₂_ge_one
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

def oriented {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (h : ℤ) (d : IntegerCoefficients X) :
    IntegerCoefficients (orientedBox h X) := by
  by_cases hn : h < 0
  · refine ⟨d.c₂, d.c₁, ?_, ?_⟩
    · simpa only [orientedBox, ite_eq_left hn, swappedBox] using d.second_eq
    · simpa only [orientedBox, ite_eq_left hn, swappedBox] using d.first_eq
  · refine ⟨d.c₁, d.c₂, ?_, ?_⟩
    · simpa only [orientedBox, ite_eq_right hn] using d.first_eq
    · simpa only [orientedBox, ite_eq_right hn] using d.second_eq

theorem coefficient_upper {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X) :
    (d.c₁ : ℝ) ≤ C * N ∧ (d.c₂ : ℝ) ≤ C * N := by
  have h₁ := (DeterminantBoxScales.coordinate_bounds X.U_ge_one X.D_ge_one X.c₁_ge_one
    (show X.U * X.D ^ 2 * X.c₁ ≤ C * N by nlinarith only [X.first_upper])).2.2
  have h₂ := (DeterminantBoxScales.coordinate_bounds X.V_ge_one X.E_ge_one X.c₂_ge_one
    (show X.V * X.E ^ 2 * X.c₂ ≤ C * N by nlinarith only [X.second_upper])).2.2
  exact ⟨by simpa only [d.first_eq] using h₁, by simpa only [d.second_eq] using h₂⟩

theorem barrier_orientation {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) :
    (orientedBox h X).c₁ * (orientedBox h X).c₂ * ((orientedBox h X).D * (orientedBox h X).E) ^ 2 =
      X.c₁ * X.c₂ * (X.D * X.E) ^ 2 := by
  by_cases hn : h < 0 <;> simp [orientedBox, hn, swappedBox, mul_comm]

end PaperP1.IntegralSourceCoefficients
