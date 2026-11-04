module

public import PaperP1.Arithmetic.ActualSourceArithmetic

/-! # The literal source height and coefficient barrier give the linear lattice step bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceLinearFibreBounds

open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.ActualProjectivePairs PaperP1.IntegralSourceCoefficients PaperP1.ZeroDegreeLinearFibres

theorem first_coefficient {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X) (p : Quad) :
    (coefficient₁ coefs.c₁ (integerPoint p).1 : ℝ) = X.c₁ * (p.1.1 : ℝ) ^ 2 := by
  rw [coefs.first_eq]
  simp [coefficient₁, integerPoint]

theorem second_coefficient {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X) (p : Quad) :
    (coefficient₂ coefs.c₂ (integerPoint p).1 : ℝ) = X.c₂ * (p.1.2 : ℝ) ^ 2 := by
  rw [coefs.second_eq]
  simp [coefficient₂, integerPoint]

theorem weighted_height {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {h : ℤ} {S : Finset Quad} (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) :
    (coefficient₁ coefs.c₁ (integerPoint p).1 : ℝ) * ((integerPoint p).2 1 : ℝ) ≤ (8 * C) * N := by
  rw [first_coefficient]
  change X.c₁ * (p.1.1 : ℝ) ^ 2 * (p.2.1 : ℝ) ≤ _
  have hc : 0 ≤ X.c₁ := by linarith [X.c₁_ge_one]
  calc
    _ ≤ X.c₁ * (2 * X.D) ^ 2 * (2 * X.U) := by
      gcongr
      · exact (hS.d_bounds p hp).2
      · exact (hS.u_bounds p hp).2
    _ = 8 * (X.c₁ * X.D ^ 2 * X.U) := by ring
    _ ≤ _ := by nlinarith only [X.first_upper]

theorem coefficient_product {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {h : ℤ} {S : Finset Quad} (hS : SignedPopulation X h S) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hbarrier : (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2) (p : Quad) (hp : p ∈ S) :
    (N : ℝ) ≤ Γ * (coefficient₁ coefs.c₁ (integerPoint p).1 : ℝ) * coefficient₂ coefs.c₂ (integerPoint p).1 := by
  rw [first_coefficient, second_coefficient]
  have hc₁ : 0 ≤ X.c₁ := by linarith [X.c₁_ge_one]
  have hc₂ : 0 ≤ X.c₂ := by linarith [X.c₂_ge_one]
  have hD : 0 ≤ X.D := by linarith [X.D_ge_one]
  have hE : 0 ≤ X.E := by linarith [X.E_ge_one]
  calc
    _ ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 := hbarrier
    _ = Γ * (X.c₁ * X.D ^ 2) * (X.c₂ * X.E ^ 2) := by ring
    _ ≤ _ := by
      gcongr
      · exact (hS.d_bounds p hp).1
      · exact (hS.e_bounds p hp).1

end PaperP1.SourceLinearFibreBounds
