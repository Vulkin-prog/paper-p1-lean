module

public import PaperP1.Asymptotics.ActualOtherLinearFactorCount

/-! # A single threshold for all actual bounded-degree linear factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformLinearFactorDegrees

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients

theorem uniform_first_count (Bmax κf : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ Amax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset Quad, SignedPopulation X h S →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeX G = 1 → 0 < degreeY G →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * T₀ := by
  choose Nd hNd using fun j : Fin (Bmax + 1) ↦
    ActualFirstLinearFactorCount.uniform_actual_first_linear_count (j.val + 1) κf (by omega) ε hε
  refine ⟨univ.sup Nd, ?_⟩
  intro N hN ρ C δ X coefs κ₀ κ₁ Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS F hcover c G hG hfirst hsecond
  have hb := ((hcover.factors c).2.1 G hG).2.2.2.1
  let j : Fin (Bmax + 1) := ⟨degreeY G - 1, by omega⟩
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans hN
  exact hNd j N hNj ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hh S hS F hcover c G hG hfirst (by dsimp [j]; omega)

theorem uniform_second_count (Amax κf : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ Bmax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset Quad, SignedPopulation X h S →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeY G = 1 → 0 < degreeX G →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * L₀ := by
  choose Nd hNd using fun j : Fin (Amax + 1) ↦
    ActualOtherLinearFactorCount.uniform_actual_second_linear_count (j.val + 1) κf (by omega) ε hε
  refine ⟨univ.sup Nd, ?_⟩
  intro N hN ρ C δ X coefs κ₀ κ₁ Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS F hcover c G hG hfirst hsecond
  have hb := ((hcover.factors c).2.1 G hG).2.2.1
  let j : Fin (Amax + 1) := ⟨degreeX G - 1, by omega⟩
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans hN
  exact hNd j N hNj ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hh S hS F hcover c G hG hfirst (by dsimp [j]; omega)

theorem uniform_bilinear_minimum_count (κf : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ Amax Bmax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset Quad, SignedPopulation X h S →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeX G = 1 → degreeY G = 1 →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * min L₀ T₀ := by
  obtain ⟨Nf, hf⟩ := ActualFirstLinearFactorCount.uniform_actual_first_linear_count 1 κf (by omega) ε hε
  obtain ⟨Ns, hs⟩ := ActualOtherLinearFactorCount.uniform_actual_second_linear_count 1 κf (by omega) ε hε
  refine ⟨max Nf Ns, ?_⟩
  intro N hN ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS F hcover c G hG hfirst hsecond
  have hT := hf N (by omega) ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hh S hS F hcover c G hG hfirst hsecond
  have hL := hs N (by omega) ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hh S hS F hcover c G hG hsecond hfirst
  rcases le_total L₀ T₀ with hLT | hTL
  · simpa only [min_eq_left hLT] using hL
  · simpa only [min_eq_right hTL] using hT

end PaperP1.UniformLinearFactorDegrees
