module

public import PaperP1.Asymptotics.ActualSourceFactorCount

/-! # All actual factors and four charts are summed at one uniform threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceClusterCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients PaperP1.GeometricFactorSwap

theorem uniform_factor_sum_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
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
      (((∑ c : Bool × Bool, ∑ G ∈ F c, (zeros G (FourProjectiveCharts.population c
        ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card) : ℕ) : ℝ) ≤
          (N : ℝ) ^ ε * min L₀ T₀ := by
  obtain ⟨Nf, hf⟩ := ActualSourceFactorCount.uniform_count hHB hNG Amax Bmax κf C ρ Kbar Abar Kshift Aexp
    (ε / 2) hC hρ hKbar hAbar hKshift hAexp (by positivity)
  obtain ⟨Nc, hc⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (4 * ((Amax + Bmax : ℕ) : ℝ)) 0 (ε / 2) (by positivity)
  refine ⟨max 1 (max Nf Nc), ?_⟩
  intro N hN δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU hM h hh hshift hMh S hS hprim F hcover
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmin : 0 ≤ min L₀ T₀ := le_min (by linarith [hcover.horizontal_ge_one]) (by linarith [hcover.vertical_ge_one])
  have hR : 0 ≤ (N : ℝ) ^ (ε / 2) * min L₀ T₀ := mul_nonneg (Real.rpow_nonneg hn.le _) hmin
  have hconstant : 4 * ((Amax + Bmax : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one] using hc N (by omega)
  have hsum (c : Bool × Bool) :
      (∑ G ∈ F c, ((zeros G (FourProjectiveCharts.population c
        ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ)) ≤
        ((Amax + Bmax : ℕ) : ℝ) * ((N : ℝ) ^ (ε / 2) * min L₀ T₀) := by
    calc
      _ ≤ ∑ _G ∈ F c, (N : ℝ) ^ (ε / 2) * min L₀ T₀ := by
        apply sum_le_sum
        intro G hG
        exact hf N (by omega) δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ M k A₀ B₀ A₁ B₁
          L₀ L₁ T₀ T₁ hD hU hM h hh hshift hMh S hS hprim F hcover c G hG
      _ = ((F c).card : ℝ) * ((N : ℝ) ^ (ε / 2) * min L₀ T₀) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hcover.factors c).1) hR
  calc
    _ = ∑ c : Bool × Bool, ∑ G ∈ F c, ((zeros G (FourProjectiveCharts.population c
        ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ ∑ _c : Bool × Bool, ((Amax + Bmax : ℕ) : ℝ) * ((N : ℝ) ^ (ε / 2) * min L₀ T₀) :=
      sum_le_sum (fun c _ ↦ hsum c)
    _ = (4 * ((Amax + Bmax : ℕ) : ℝ)) * ((N : ℝ) ^ (ε / 2) * min L₀ T₀) := by
      simp [Fintype.card_prod, mul_assoc]
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * min L₀ T₀) :=
      mul_le_mul_of_nonneg_right hconstant hR
    _ = ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * min L₀ T₀ := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem uniform_cluster_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
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
      ((cluster M X.D X.E k S).card : ℝ) ≤ (N : ℝ) ^ ε * min L₀ T₀ := by
  obtain ⟨N₀, hN₀⟩ := uniform_factor_sum_count hHB hNG Amax Bmax κf C ρ Kbar Abar Kshift Aexp
    ε hC hρ hKbar hAbar hKshift hAexp hε
  refine ⟨N₀, ?_⟩
  intro N hN δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU hM h hh hshift hMh S hS hprim F hcover
  have hhcount := hN₀ N hN δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ M k A₀ B₀ A₁ B₁
    L₀ L₁ T₀ T₁ hD hU hM h hh hshift hMh S hS hprim F hcover
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast hcover.count).trans hhcount

end PaperP1.ActualSourceClusterCount
