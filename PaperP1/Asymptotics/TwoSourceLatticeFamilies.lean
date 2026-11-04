module

public import PaperP1.Asymptotics.UniformHorizontalLatticeFamily
public import PaperP1.Asymptotics.UniformVerticalLatticeFamily

/-! # Both actual source lattice families and side sums hold simultaneously -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSourceLatticeFamilies

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantRelativeIntervals PaperP1.QuadraticIntervalGrid

theorem uniform_two_families (ε C ρ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ κ₀ κ₁ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ,
      ∃ A₀ B₀ A₁ B₁ : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ T₀ T₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → HorizontalGridCoordinateData.Data X κ₀ M k (A₀ k) (B₀ k) (L₀ k) (L₁ k)) ∧
        (∀ q : ℕ, q ≤ 4 * M → VerticalGridCoordinateData.Data X κ₁ M q (A₁ q) (B₁ q) (T₀ q) (T₁ q)) ∧
        ∀ I : Finset ℕ, (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) →
          ((∑ k ∈ I, L₀ k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (X.D * X.E * M) + 32 * X.E + 8 * X.D) ∧
          ((∑ k ∈ I, T₀ (grid M k)) ≤
            (512 * (2 * (49 + 16 / ρ)) * C / ρ) * (N : ℝ) ^ ε *
              (Real.sqrt (X.U * X.V * M) + X.U + X.V)) := by
  obtain ⟨κ₀, ND, hhorizontal⟩ := UniformHorizontalLatticeFamily.uniform_family_sum ε C hε hC
  obtain ⟨κ₁, NU, hvertical⟩ := UniformVerticalLatticeFamily.uniform_family_sum ε C ρ hε hC hρ
  refine ⟨κ₀, κ₁, max ND NU, ?_⟩
  intro N hN M hM hMN δ X
  obtain ⟨A₀, B₀, L₀, L₁, hD, hDsum⟩ := hhorizontal N (by omega) M (by omega) (by omega) ρ δ X
  obtain ⟨A₁, B₁, T₀, T₁, hU, hUsum⟩ := hvertical N (by omega) M hM hMN δ X
  refine ⟨A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hD, hU, ?_⟩
  intro I hlow hupper
  have hI : I ⊆ intervalIndices M := by
    intro k hk
    have hlo := hlow k hk
    exact mem_Icc.mpr ⟨by omega, hupper k hk⟩
  have hlowR : ∀ k ∈ I, (M : ℝ) / 4 ≤ k := by
    intro k hk
    have hlo : (M : ℝ) ≤ 4 * k := by exact_mod_cast hlow k hk
    linarith
  exact ⟨hDsum I hI hlowR, hUsum I hlow hupper⟩

end PaperP1.TwoSourceLatticeFamilies
