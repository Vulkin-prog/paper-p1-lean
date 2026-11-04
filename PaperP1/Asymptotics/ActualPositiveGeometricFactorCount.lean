module

public import PaperP1.Asymptotics.ActualGeometricFactorCount
public import PaperP1.Asymptotics.UniformLinearFactorDegrees

/-! # Every positive-bidegree geometric source factor has the minimum-side count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualPositiveGeometricFactorCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients PaperP1.GeometricFactorSwap

theorem uniform_actual_count (hHB : HeathBrownBiformInput.Input) (Amax Bmax κf : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset Quad, SignedPopulation X h S →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, Geometric G → 0 < degreeX G → 0 < degreeY G →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * min L₀ T₀ := by
  obtain ⟨Nf, hf⟩ := ActualGeometricFactorCount.uniform_first_count hHB Amax Bmax κf ρ hρ ε hε
  obtain ⟨Ns, hs⟩ := ActualGeometricFactorCount.uniform_second_count hHB Amax Bmax κf ρ hρ ε hε
  obtain ⟨Nlf, hlf⟩ := UniformLinearFactorDegrees.uniform_first_count Bmax κf ε hε
  obtain ⟨Nls, hls⟩ := UniformLinearFactorDegrees.uniform_second_count Amax κf ε hε
  refine ⟨max Nf (max Ns (max Nlf Nls)), ?_⟩
  intro N hN C δ X coefs κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS F hcover c G hG hgeo hfirst hsecond
  have hL : ((zeros G (FourProjectiveCharts.population c
      ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * L₀ := by
    by_cases hb : 2 ≤ degreeY G
    · exact hf N (by omega) C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU
        _ F hcover c G hG hgeo hfirst hb
    · exact hls N (by omega) ρ C δ X coefs κ₀ κ₁ Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
        hD hU h hh S hS F hcover c G hG (by omega) hfirst
  have hT : ((zeros G (FourProjectiveCharts.population c
      ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * T₀ := by
    by_cases ha : 2 ≤ degreeX G
    · exact hs N (by omega) C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU
        _ F hcover c G hG hgeo ha hsecond
    · exact hlf N (by omega) ρ C δ X coefs κ₀ κ₁ Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
        hD hU h hh S hS F hcover c G hG (by omega) hsecond
  rcases le_total L₀ T₀ with hLT | hTL
  · simpa only [min_eq_left hLT] using hL
  · simpa only [min_eq_right hTL] using hT

end PaperP1.ActualPositiveGeometricFactorCount
