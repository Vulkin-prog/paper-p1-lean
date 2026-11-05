module

public import PaperP1.Diophantine.GeometricBiformPointCount
public import PaperP1.Algebra.ComplexProjectiveIrreducibility
public import PaperP1.Asymptotics.CompanionUniformDeterminantTheorem
public import PaperP1.Asymptotics.CompanionTwoSmallKernelTheorem
public import PaperP1.Asymptotics.FixedWidthTwoSmallKernel

/-! # Unconditional canonical companion kernel counts

Both geometric and non-geometric biform counts are supplied by their internal
proofs. Original populations, source parameters and quantifier orders are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompanionKernelCounts

open Finset PaperP1.InitialDyadicSourceBox PaperP1.DeterminantLogScale
  PaperP1.CompanionUniformDeterminantTheorem PaperP1.TwoSmallKernelWindows
  PaperP1.ComplexProjectiveIrreducibility

theorem weakened_barrier_count
    (δ C ρ Kbar Abar K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 →
      ((solutions X h).card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  exact PaperP1.CompanionUniformDeterminantTheorem.weakened_barrier_count GeometricBiformPointCount.full_input nongeometric_input
    δ C ρ Kbar Abar K A ε hδ hC hρ hρ₁ hKbar hAbar hK hA hε

theorem companion_T1_4
    (A₀ δ ε ρ C : ℝ) (hA₀ : 0 < A₀) (hδ : 0 < δ) (hε : 0 < ε)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ (Real.log N) ^ A₀ →
      ∀ X : Box N ρ C δ, (N : ℝ) ≤ (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 →
      ((solutions X h).card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  exact PaperP1.CompanionUniformDeterminantTheorem.companion_T1_4 GeometricBiformPointCount.full_input nongeometric_input
    A₀ δ ε ρ C hA₀ hδ hε hρ hρ₁ hC

theorem companion_T1_5
    (β D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (max β (7 / 12) + ε) := by
  exact PaperP1.CompanionTwoSmallKernelTheorem.companion_T1_5 GeometricBiformPointCount.full_input nongeometric_input
    β D ε hD hε

theorem companion_T1_5_sharp
    (β D ε : ℝ) (hβlo : 7 / 12 ≤ β) (hβhi : β < 1) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, 2 ≤ L →
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      (N : ℝ) ^ (β - ε) ≤ ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ∧
        ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (β + ε) := by
  exact PaperP1.CompanionTwoSmallKernelTheorem.companion_T1_5_sharp GeometricBiformPointCount.full_input nongeometric_input
    β D ε hβlo hβhi hD hε

theorem companion_T1_13
    (a K D E θ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * Real.log N →
      ∀ G : Finset ℤ, (∀ x ∈ G, a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ K * N) →
      ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * Real.log N) →
      (∀ T : ℝ, 0 ≤ T → ((FixedWidthSmallKernel.realSelectedStarts G V Y T).card : ℝ) ≤
        (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T) ∧
      ((PaperP1.FixedWidthTwoSmallKernel.realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (max θ (7 / 12) + ε) ∧
      (7 / 12 ≤ θ → ((PaperP1.FixedWidthTwoSmallKernel.realSelectedStarts G V Y ((N : ℝ) ^ θ)).card : ℝ) ≤ (N : ℝ) ^ (θ + ε)) := by
  exact PaperP1.FixedWidthTwoSmallKernel.companion_T1_13 GeometricBiformPointCount.full_input nongeometric_input
    a K D E θ ε ha hD hE hε

end PaperP1.CompanionKernelCounts
