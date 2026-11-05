module

public import PaperP1.Diophantine.ImaginaryQuadraticCount
public import PaperP1.Diophantine.PositiveDiscriminantConicCount
public import PaperP1.Algebra.ConicIrreducibility

/-! # Negative-discriminant conic counts from the actual imaginary norm equation

At polynomial coefficient height, the count covers all integral zeros without
any point-height restriction. Geometric irreducibility supplies non-degeneracy.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NegativeDiscriminantConicCount

open Polynomial Finset ConicNormCoordinates ConicPolynomialPresentation
open GeometricFactorSwap

theorem coefficient_nonzero (Q : Coefficients) (hΔ : discriminant Q < 0) : Q.c ≠ 0 := by
  intro hc
  have he : discriminant Q = Q.b ^ 2 := by simp [discriminant, hc]
  rw [he] at hΔ
  exact (not_lt_of_ge (sq_nonneg Q.b)) hΔ

theorem count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : Coefficients, discriminant Q < 0 →
      normConstant Q ≠ 0 → height Q ≤ N ^ K →
      ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, value Q z.1 z.2 = 0) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := ImaginaryQuadraticCount.count_le_rpow_eventually (4 * K + 8) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN Q hΔ hδ hM S hS
  let D := (discriminant Q).natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr (ne_of_lt hΔ)
  have hDcast : (D : ℤ) = -discriminant Q := by
    change ((discriminant Q).natAbs : ℤ) = _
    rw [Int.natCast_natAbs, abs_of_neg hΔ]
  have hδb := (PositiveDiscriminantConicCount.polynomial_budget Q N K 0
    (by omega) hM (Nat.zero_le _)).2.1
  have hb := hN₀ N (by omega) D (normConstant Q) hD hδ hδb (S.image (transform Q)) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    rw [hDcast]
    simpa only [neg_mul, sub_eq_add_neg] using zero_maps_to_norm Q z (hS z hz))
  simpa only [card_image_of_injective _
    (transform_injective Q (coefficient_nonzero Q hΔ) (ne_of_lt hΔ))] using hb

theorem finite_population_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P ≤ 2 →
      Geometric P → discriminant (coefficients P) < 0 → BivariateHeight.height P ≤ N ^ K →
      ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, P.evalEval z.1 z.2 = 0) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := count (K + 3) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN P hD hgeo hΔ hM S hS
  have hδ : normConstant (coefficients P) ≠ 0 := by
    apply ConicIrreducibility.geometric_normConstant_ne_zero (coefficients P)
      (coefficient_nonzero _ hΔ)
    rwa [reconstruction P hD]
  have hheight : height (coefficients P) ≤ N ^ (K + 3) :=
    (height_coefficients P).trans ((Nat.mul_le_mul_left 6 hM).trans
      (PositiveDiscriminantConicCount.constant_mul_power N (by omega) 6 3 K (by decide)))
  apply hN₀ N (by omega) (coefficients P) hΔ hδ hheight S
  intro z hz
  rw [← evaluation, reconstruction P hD]
  exact hS z hz

theorem grid_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P ≤ 2 →
      Geometric P → discriminant (coefficients P) < 0 → BivariateHeight.height P ≤ N ^ K →
      ∀ B : ℕ, ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := finite_population_count K ε hε
  refine ⟨N₀, ?_⟩
  intro N hN P hD hgeo hΔ hM B
  exact hN₀ N hN P hD hgeo hΔ hM (PlaneCurvePointCount.grid P B)
    (fun z hz ↦ ((PlaneCurvePointCount.mem_grid P B z).mp hz).2.2)

end PaperP1.NegativeDiscriminantConicCount
