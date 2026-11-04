module

public import PaperP1.Asymptotics.ActualPositiveGeometricFactorCount
public import PaperP1.Asymptotics.ActualNonGeometricFactorCount
public import PaperP1.Asymptotics.ActualZeroFirstDegreeCount
public import PaperP1.Asymptotics.PolylogSourceBarrierCount

/-! # All actual factor branches have one uniform minimum-side count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceFactorCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients PaperP1.GeometricFactorSwap

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (Amax Bmax κf : ℕ) (C ρ Kbar Abar Kshift Aexp ε : ℝ)
    (hC : 0 < C) (hρ : 0 < ρ) (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar)
    (hKshift : 0 ≤ Kshift) (hAexp : 0 ≤ Aexp) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ κ₀ κ₁ M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      1 ≤ M → ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      (M : ℝ) * |(h : ℝ)| ≤ N → ∀ S : Finset Quad, SignedPopulation X h S →
      (∀ p ∈ S, Primitive p) → ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c,
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * min L₀ T₀ := by
  obtain ⟨Np, hp⟩ := ActualZeroFirstDegreeCount.uniform_normalized_actual_count Bmax C hC ε hε
  obtain ⟨Nl, hl⟩ := PolylogSourceBarrierCount.uniform_actual_count Amax C Kbar Abar Kshift Aexp ε
    hC.le hKbar hAbar hKshift hAexp hε
  obtain ⟨Ng, hg⟩ := ActualPositiveGeometricFactorCount.uniform_actual_count hHB Amax Bmax κf ρ hρ ε hε
  obtain ⟨Nn, hn⟩ := ActualNonGeometricFactorCount.uniform_actual_minimum_count hNG Amax Bmax ε hε
  refine ⟨max Np (max Nl (max Ng Nn)), ?_⟩
  intro N hN δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU hM h hh hshift hMh S hS hprim F hcover c G hG
  have hsmall (hc : ((zeros G (FourProjectiveCharts.population c
      ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε) :
      ((zeros G (FourProjectiveCharts.population c
        ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * min L₀ T₀ := by
    have hmin : 1 ≤ min L₀ T₀ := le_min hcover.horizontal_ge_one hcover.vertical_ge_one
    have hmul := mul_le_mul_of_nonneg_left hmin (Real.rpow_nonneg (Nat.cast_nonneg N) ε)
    exact hc.trans (by simpa only [mul_one] using hmul)
  by_cases hx : degreeX G = 0
  · apply hsmall
    exact hp N (by omega) ρ δ X coefs κ₀ κ₁ κf Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
      hD hU hM h hh hMh S hS hprim F hcover c G hG hx
  · by_cases hy : degreeY G = 0
    · apply hsmall
      exact hl N (by omega) ρ δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ κf Bmax M k A₀ B₀ A₁ B₁
        L₀ L₁ T₀ T₁ hD hU h hh hshift S hS hprim F hcover c G hG hy
    · by_cases hgeo : Geometric G
      · exact hg N (by omega) C δ X coefs κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
          hD hU h hh S hS F hcover c G hG hgeo (by omega) (by omega)
      · exact hn N (by omega) κf (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F hcover c G hG hgeo (by omega) (by omega)

end PaperP1.ActualSourceFactorCount
