module

public import PaperP1.Asymptotics.ActualZeroSecondDegreeCount
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Both the short shift and a polylogarithmic source-barrier loss are absorbed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogSourceBarrierCount

open Filter Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients

theorem uniform_budget (a : ℕ) (C Kbar Abar Kshift Aexp ε : ℝ)
    (hC : 0 ≤ C) (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (_hKshift : 0 ≤ Kshift)
    (hAexp : 0 ≤ Aexp) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Γ H : ℝ, 0 ≤ Γ → 0 ≤ H →
      Γ ≤ Kbar * (Real.log N) ^ Abar → H ≤ Kshift * (Real.log N) ^ Aexp →
      2 * (a + 1) * (Γ * (8 * C) * H + 1) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Np, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (2 * (a + 1) * (8 * C * Kbar * Kshift + 1)) (Abar + Aexp) ε hε
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1))
  refine ⟨max Np Nl, ?_⟩
  intro N hN Γ H hΓ hH hbar hshift
  have hlog : 1 ≤ Real.log N := hl N (by omega)
  have hlogpos : 0 < Real.log N := by linarith
  have hprod : Γ * H ≤ (Kbar * Kshift) * (Real.log N) ^ (Abar + Aexp) := by
    calc
      _ ≤ (Kbar * (Real.log N) ^ Abar) * (Kshift * (Real.log N) ^ Aexp) :=
        mul_le_mul hbar hshift hH (by positivity)
      _ = _ := by rw [Real.rpow_add hlogpos]; ring
  have hpow : 1 ≤ (Real.log N) ^ (Abar + Aexp) := Real.one_le_rpow hlog (add_nonneg hAbar hAexp)
  have hcprod := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 8 * C)
  calc
    _ ≤ (2 * (a + 1) * (8 * C * Kbar * Kshift + 1)) * (Real.log N) ^ (Abar + Aexp) := by
      have hinner : Γ * (8 * C) * H + 1 ≤
          (8 * C * Kbar * Kshift + 1) * (Real.log N) ^ (Abar + Aexp) := by
        nlinarith only [hcprod, hpow]
      have hh := mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2 * (a + 1))
      nlinarith only [hh]
    _ ≤ _ := hp N (by omega)

theorem uniform_actual_count (Amax : ℕ) (C Kbar Abar Kshift Aexp ε : ℝ)
    (hC : 0 ≤ C) (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hKshift : 0 ≤ Kshift)
    (hAexp : 0 ≤ Aexp) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ κ₀ κ₁ κf Bmax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      ∀ S : Finset Quad, SignedPopulation X h S → (∀ p ∈ S, Primitive p) →
      ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeY G = 0 →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_budget Amax C Kbar Abar Kshift Aexp ε hC hKbar hAbar hKshift hAexp hε
  refine ⟨N₀, ?_⟩
  intro N hN ρ δ X coefs Γ hΓ hΓbound hbarrier κ₀ κ₁ κf Bmax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh hshift S hS hprim F hcover c G hG hsecond
  have hcount := ActualZeroSecondDegreeCount.actual_count hC X coefs κ₀ κ₁ κf Amax Bmax M k
    A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hh S hS hprim F hcover c G hG hsecond Γ hΓ hbarrier
  exact hcount.trans (hN₀ N hN Γ h.natAbs hΓ (Nat.cast_nonneg _) hΓbound
    (by simpa only [Nat.cast_natAbs, Int.cast_abs] using hshift))

end PaperP1.PolylogSourceBarrierCount
