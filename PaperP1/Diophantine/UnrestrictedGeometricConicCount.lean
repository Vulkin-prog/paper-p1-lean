module

public import PaperP1.Diophantine.UnrestrictedHyperbolicConicCount
public import PaperP1.Diophantine.UnrestrictedEllipticConicCount
public import PaperP1.Diophantine.UnrestrictedParabolicConicCount

/-! # Full coefficient-uniform geometric conic counts

The three discriminant cases are proved internally. The exponent is 1/2+epsilon;
this does not assert the stronger degree-uniform BCN logarithmic estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnrestrictedGeometricConicCount

open Polynomial Finset Filter ConicNormCoordinates ConicPolynomialPresentation
open GeometricFactorSwap

theorem natural_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → ((PlaneCurvePointCount.grid P N).card : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨Nh, _hNh, hh⟩ := UnrestrictedHyperbolicConicCount.natural_count ε hε
  obtain ⟨Ne, _hNe, he⟩ := UnrestrictedEllipticConicCount.natural_count ε hε
  obtain ⟨Np, _hNp, hp⟩ := UnrestrictedParabolicConicCount.natural_count ε hε
  refine ⟨max 3 (max Nh (max Ne Np)), by omega, ?_⟩
  intro N hN P hD hgeo
  have hpow : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  rcases lt_trichotomy (discriminant (coefficients P)) 0 with hneg | hzero | hpos
  · exact (he N (by omega) P hD hgeo hneg).trans hpow
  · exact hp N (by omega) P hD hgeo hzero
  · exact (hh N (by omega) P hD hgeo hpos).trans hpow

theorem finite_population_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → ∀ S : Finset (ℤ × ℤ),
      (∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀, hcount⟩ := natural_count ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN P hD hgeo S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    have hh := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hh.1⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.1
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.2
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (hcount N hN P hD hgeo)

theorem polynomial_height_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → ∀ B : ℕ, B ≤ N ^ K →
        ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ (N : ℝ) ^ ((K : ℝ) / 2 + ε) := by
  let θ := ε / ((K : ℝ) + 1)
  let δ := (1 : ℝ) / 2 + θ
  let ζ := (K : ℝ) / 2 + ε
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  have hcancel : ((K : ℝ) + 1) * θ = ε := by dsimp only [θ]; field_simp
  have hbudget : (K : ℝ) * δ ≤ ζ := by dsimp only [δ, ζ]; nlinarith
  obtain ⟨B₀, _hB₀, hcount⟩ := natural_count θ hθ
  have ht := ((tendsto_rpow_atTop hζ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop ((B₀ : ℝ) ^ δ))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ht
  refine ⟨max 2 N₁, by omega, ?_⟩
  intro N hN P hD hgeo B hBN
  by_cases hsmall : B < B₀
  · have hB : (B : ℤ) ≤ (B₀ : ℤ) := by exact_mod_cast hsmall.le
    have hsub : PlaneCurvePointCount.grid P B ⊆ PlaneCurvePointCount.grid P B₀ := by
      intro z hz
      have hh := (PlaneCurvePointCount.mem_grid P B z).mp hz
      exact (PlaneCurvePointCount.mem_grid P B₀ z).mpr ⟨hh.1.trans hB, hh.2.1.trans hB, hh.2.2⟩
    have hc : ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ ((PlaneCurvePointCount.grid P B₀).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact (hc.trans (hcount B₀ le_rfl P hD hgeo)).trans (hN₁ N (by omega))
  · have hc := hcount B (by omega) P hD hgeo
    have hBR : (B : ℝ) ≤ (N : ℝ) ^ K := by exact_mod_cast hBN
    have hpow : (B : ℝ) ^ δ ≤ (N : ℝ) ^ ζ := by
      calc
        _ ≤ ((N : ℝ) ^ K) ^ δ := Real.rpow_le_rpow (Nat.cast_nonneg B) hBR (by dsimp only [δ]; positivity)
        _ = (N : ℝ) ^ ((K : ℝ) * δ) := by rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N) K δ]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hbudget
    exact hc.trans hpow

end PaperP1.UnrestrictedGeometricConicCount
