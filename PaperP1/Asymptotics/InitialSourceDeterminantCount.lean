module

public import PaperP1.Analysis.InitialDeterminantShape
public import PaperP1.Asymptotics.NonprimitiveSourceDeterminantCount

/-! # The full signed determinant count at arbitrary positive original real scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InitialSourceDeterminantCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.InitialDyadicSourceBox PaperP1.DeterminantLogScale

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, (N : ℝ) ≤ (X.c₁ : ℝ) * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, Population X h S →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  classical
  obtain ⟨Nf, hf⟩ := NonprimitiveSourceDeterminantCount.uniform_signed_count hHB hNG δ (8 * C) ρ K A (ε / 2)
    hδ (by positivity) hρ hρ₁ hK hA (by positivity)
  obtain ⟨Nc, hc⟩ := InitialDeterminantShape.uniform_cost_comparison C (ε / 2) hC (by positivity)
  refine ⟨max 1 (max Nf Nc), ?_⟩
  intro N hN h hh hshift X hbarrier S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let F := Real.exp (logShape N X.D X.E X.U X.V)
  let cost := min (Real.sqrt (X.D * X.E * F) + X.D + X.E) (Real.sqrt (X.U * X.V * F) + X.U + X.V)
  change (S.card : ℝ) ≤ (N : ℝ) ^ ε * cost
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hd := X.D_pos.le
    have he := X.E_pos.le
    have hu := X.U_pos.le
    have hv := X.V_pos.le
    simp only [card_empty, Nat.cast_zero]
    dsimp only [cost]
    positivity
  · have hhalf := half_scales hS hne
    let Y := normalize X hhalf
    let F' := Real.exp (logShape N Y.D Y.E Y.U Y.V)
    let cost' := min (Real.sqrt (Y.D * Y.E * F') + Y.D + Y.E) (Real.sqrt (Y.U * Y.V * F') + Y.U + Y.V)
    have hbarrier' : (N : ℝ) ≤ Y.c₁ * Y.c₂ * (Y.D * Y.E) ^ 2 :=
      hbarrier.trans (normalized_barrier X hhalf)
    have hcount : (S.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) * cost' :=
      hf N (by omega) h hh hshift Y (coefficients X hhalf) hbarrier' S (normalized_population X hhalf h S hS)
    obtain ⟨hc₁, hc₂⟩ := hc N (by omega) ρ δ hδ.le X hhalf
    have hcost : cost' ≤ (N : ℝ) ^ (ε / 2) * cost := by
      dsimp only [cost', cost]
      rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hn.le (ε / 2))]
      exact min_le_min hc₁ hc₂
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * cost' := hcount
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * cost) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

end PaperP1.InitialSourceDeterminantCount
