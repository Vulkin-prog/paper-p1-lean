module

public import PaperP1.Asymptotics.HeathBrownHeightBudget
public import PaperP1.Asymptotics.SourceLargeSidesHeight

/-! # The ordinary geometric input counts the actual bounded-degree factor populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualGeometricFactorCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.TwoKernelDeterminantBoxes
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.GeometricFactorSwap

theorem uniform_first_count (hHB : HeathBrownBiformInput.Input) (Amax Bmax κf : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ κ₀ κ₁ M k : ℕ,
      ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ Q : Finset Quad, ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax Q B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, Geometric G → 0 < degreeX G → 2 ≤ degreeY G →
        ((zeros G (FourProjectiveCharts.population c (Q.image (coordinates B₀ B₁)))).card : ℝ) ≤
          (N : ℝ) ^ ε * L₀ := by
  obtain ⟨Nh, hh⟩ := SourceLargeSidesHeight.uniform_height ρ hρ
  choose Nd hNd using fun j : Fin (Amax + 1) × Fin (Bmax + 1) ↦
    HeathBrownHeightBudget.uniform_first_count hHB (j.1.val + 1) (j.2.val + 2) 5 κf (by omega) (by omega) ε hε
  refine ⟨max Nh (univ.sup Nd), ?_⟩
  intro N hN C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU Q F hcover c G hG hgeo hfirst hsecond
  have hfactor := (hcover.factors c).2.1 G hG
  have hheight := hh N (by omega) C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU
  let j : Fin (Amax + 1) × Fin (Bmax + 1) :=
    (⟨degreeX G - 1, by have := hfactor.2.2.1; omega⟩,
      ⟨degreeY G - 2, by have := hfactor.2.2.2.1; omega⟩)
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans (le_max_right _ _ |>.trans hN)
  apply hNd j N hNj G (by dsimp [j]; omega) (by dsimp [j]; omega) hgeo hfactor.2.2.2.2.1
    L₀ hcover.horizontal_ge_one hheight.1
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.1, hpoint.2.1⟩
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact (IntegerPairFactorCharts.projective_zero_iff G p.1 p.2 hpoint.2.2.1 hpoint.2.2.2.1).mpr
      (mem_filter.mp hp).2
  · intro p hp
    exact (hcover.chart_points c p (mem_filter.mp hp).1).2.2.2.2.1

theorem uniform_second_count (hHB : HeathBrownBiformInput.Input) (Amax Bmax κf : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ κ₀ κ₁ M k : ℕ,
      ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ Q : Finset Quad, ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax Q B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, Geometric G → 2 ≤ degreeX G → 0 < degreeY G →
        ((zeros G (FourProjectiveCharts.population c (Q.image (coordinates B₀ B₁)))).card : ℝ) ≤
          (N : ℝ) ^ ε * T₀ := by
  obtain ⟨Nh, hh⟩ := SourceLargeSidesHeight.uniform_height ρ hρ
  choose Nd hNd using fun j : Fin (Amax + 1) × Fin (Bmax + 1) ↦
    HeathBrownHeightBudget.uniform_second_count hHB (j.1.val + 2) (j.2.val + 1) 5 κf (by omega) (by omega) ε hε
  refine ⟨max Nh (univ.sup Nd), ?_⟩
  intro N hN C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU Q F hcover c G hG hgeo hfirst hsecond
  have hfactor := (hcover.factors c).2.1 G hG
  have hheight := hh N (by omega) C δ X κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU
  let j : Fin (Amax + 1) × Fin (Bmax + 1) :=
    (⟨degreeX G - 2, by have := hfactor.2.2.1; omega⟩,
      ⟨degreeY G - 1, by have := hfactor.2.2.2.1; omega⟩)
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans (le_max_right _ _ |>.trans hN)
  apply hNd j N hNj G (by dsimp [j]; omega) (by dsimp [j]; omega) hgeo hfactor.2.2.2.2.1
    T₀ hcover.vertical_ge_one hheight.2
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.1, hpoint.2.1⟩
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact (IntegerPairFactorCharts.projective_zero_iff G p.1 p.2 hpoint.2.2.1 hpoint.2.2.2.1).mpr
      (mem_filter.mp hp).2
  · intro p hp
    exact (hcover.chart_points c p (mem_filter.mp hp).1).2.2.2.2.2

end PaperP1.ActualGeometricFactorCount
