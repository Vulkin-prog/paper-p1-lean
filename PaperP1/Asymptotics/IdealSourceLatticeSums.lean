module

public import PaperP1.Analysis.RoundedScaleSideBudget
public import PaperP1.Asymptotics.RoundedSourceLatticeFamilies

/-! # Both actual lattice side sums at the ideal paper scale, with all rounding losses absorbed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IdealSourceLatticeSums

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantRelativeIntervals PaperP1.QuadraticIntervalGrid
open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale

theorem uniform_ideal_sums (ε η C ρ K A ζ : ℝ) (hη : 0 < η) (hC : 0 < C) (hρ : 0 < ρ)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) (hgap : η + ζ / 2 < ε) :
    ∃ κ₀ κ₁ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ,
      let M := horizontalScale N X.D X.E X.U X.V ζ
      let S := Real.exp (logShape N X.D X.E X.U X.V)
      32 ≤ M ∧ 2 * M ≤ N ∧ (M : ℝ) * |(h : ℝ)| ≤ N ∧
      ∃ A₀ B₀ A₁ B₁ : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ T₀ T₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → HorizontalGridCoordinateData.Data X κ₀ M k (A₀ k) (B₀ k) (L₀ k) (L₁ k)) ∧
        (∀ q : ℕ, q ≤ 4 * M → VerticalGridCoordinateData.Data X κ₁ M q (A₁ q) (B₁ q) (T₀ q) (T₁ q)) ∧
        ∀ I : Finset ℕ, (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) →
          ((∑ k ∈ I, L₀ k) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * S) + X.D + X.E)) ∧
          ((∑ k ∈ I, T₀ (grid M k)) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * S) + X.U + X.V)) := by
  let Q := η + ζ / 2
  let Kvert := 512 * (2 * (49 + 16 / ρ)) * C / ρ
  have hroom : 0 < ε - Q := by dsimp [Q]; linarith
  obtain ⟨κ₀, κ₁, NF, hfamilies⟩ := RoundedSourceLatticeFamilies.uniform_rounded_families η C ρ K A ζ hη hC hρ hζ hζsmall
  obtain ⟨NH, hhorizontal⟩ := HalfCountSchedule.factor_absorption 160 Q (ε - Q) hroom
  obtain ⟨NV, hvertical⟩ := HalfCountSchedule.factor_absorption (2 * Kvert) Q (ε - Q) hroom
  refine ⟨κ₀, κ₁, max 2 (max NF (max NH NV)), ?_⟩
  intro N hN h hh hshift δ X
  let M := horizontalScale N X.D X.E X.U X.V ζ
  let S := Real.exp (logShape N X.D X.E X.U X.V)
  obtain ⟨hM, hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, hsums⟩ :=
    hfamilies N (by omega) h hh hshift δ X
  refine ⟨hM, hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, ?_⟩
  intro I hlow hupper
  have hraw := hsums I hlow hupper
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hD : 0 ≤ X.D := by linarith [X.D_ge_one]
  have hE : 0 ≤ X.E := by linarith [X.E_ge_one]
  have hU : 0 ≤ X.U := by linarith [X.U_ge_one]
  have hV : 0 ≤ X.V := by linarith [X.V_ge_one]
  have hS : 0 ≤ S := (Real.exp_pos _).le
  have hMupper : (M : ℝ) ≤ 2 * (N : ℝ) ^ ζ * S := RoundedScaleSideBudget.rounded_upper hN2
    X.D_ge_one X.E_ge_one X.U_ge_one X.V_ge_one hζ.le
  have hH : 160 * (N : ℝ) ^ Q ≤ (N : ℝ) ^ ε := by
    simpa only [show Q + (ε - Q) = ε by ring] using hhorizontal N (by omega)
  have hVcost : (2 * Kvert) * (N : ℝ) ^ Q ≤ (N : ℝ) ^ ε := by
    simpa only [show Q + (ε - Q) = ε by ring] using hvertical N (by omega)
  have hKvert : 0 ≤ Kvert := by dsimp [Kvert]; positivity
  constructor
  · calc
      _ ≤ 60 * (N : ℝ) ^ η * Real.sqrt (X.D * X.E * M) + 32 * X.E + 8 * X.D := hraw.1
      _ ≤ 160 * (N : ℝ) ^ Q * (Real.sqrt (X.D * X.E * S) + X.D + X.E) :=
        RoundedScaleSideBudget.horizontal_cost N M hN1 hD hE hS hη.le hζ.le hMupper
      _ ≤ _ := mul_le_mul_of_nonneg_right hH (by positivity)
  · calc
      _ ≤ Kvert * (N : ℝ) ^ η * (Real.sqrt (X.U * X.V * M) + X.U + X.V) := hraw.2
      _ ≤ (2 * Kvert) * (N : ℝ) ^ Q * (Real.sqrt (X.U * X.V * S) + X.U + X.V) :=
        RoundedScaleSideBudget.vertical_cost N M hN1 hU hV hS hKvert hζ.le hMupper
      _ ≤ _ := mul_le_mul_of_nonneg_right hVcost (by positivity)

end PaperP1.IdealSourceLatticeSums
