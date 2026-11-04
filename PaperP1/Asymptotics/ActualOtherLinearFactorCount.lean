module

public import PaperP1.Diophantine.ActualSecondLinearFactorCount
public import PaperP1.Asymptotics.ActualFirstLinearFactorCount
public import PaperP1.Diophantine.ActualIntegerSourceEquation
public import PaperP1.Asymptotics.ConstructedClusterCurveData

/-! # The actual second-degree-one source populations are counted -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualOtherLinearFactorCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients

theorem uniform_actual_second_linear_count (d κf : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ Amax Bmax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → ∀ S : Finset Quad, SignedPopulation X h S →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeY G = 1 → degreeX G = d →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε * L₀ := by
  obtain ⟨N₀, hN₀⟩ := ActualSecondLinearFactorCount.uniform_count 2 1 d κf hd (by omega) ε hε
  refine ⟨N₀, ?_⟩
  intro N hN ρ C δ X coefs κ₀ κ₁ Amax Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS F hcover c G hG hfirst hsecond
  have hfactor := (hcover.factors c).2.1 G hG
  apply hN₀ N hN G hfactor.1 hfirst hsecond hfactor.2.2.2.2.1
    (ActualIntegerSourceEquation.chartFamily coefs A₀ A₁ c)
    (ActualIntegerSourceEquation.chart_homogeneous coefs A₀ A₁ c) h hh L₀ T₀
    hcover.horizontal_ge_one (by linarith [hcover.vertical_ge_one])
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.1, hpoint.2.1⟩
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact (IntegerPairFactorCharts.projective_zero_iff G p.1 p.2 hpoint.2.2.1 hpoint.2.2.2.1).mpr
      (mem_filter.mp hp).2
  · exact ActualIntegerSourceEquation.factor_population_value coefs A₀ B₀ A₁ B₁
      hD.right_inverse hU.right_inverse h _ (ActualFirstLinearFactorCount.cluster_population hS M k) c G
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2⟩

end PaperP1.ActualOtherLinearFactorCount
