module

public import PaperP1.Diophantine.GeometricHyperbolicConicCount
public import PaperP1.Algebra.ConicScalarInvariants
public import PaperP1.Arithmetic.SmallHeightAssociatedPlanePresentation

/-! # Coefficient-height-free hyperbolic conic counts on the full original grid

Every coefficient is unrestricted. Bounded-height normalization, rational
association and discriminant-sign preservation are supplied internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnrestrictedHyperbolicConicCount

open Polynomial Finset Filter PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation
open PaperP1.GeometricFactorSwap PaperP1.RationalBivariateIrreducibility PaperP1.PolynomialScalarProjection

theorem natural_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → 0 < discriminant (coefficients P) →
        ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  classical
  let r := Fintype.card (TotalDegreeMonomials.Index 2)
  let κ := 2 * (r - 1)
  let Cnat := (6 * r) ^ (r - 1)
  obtain ⟨Nq, hq⟩ := GeometricHyperbolicConicCount.natural_height_count (κ + 1) ε hε
  have ht := ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (4 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 3 (max Nq (max Cnat Nc)), by omega, ?_⟩
  intro N hN P hD hgeo hΔ
  let S := PlaneCurvePointCount.grid P N
  by_cases hsmall : S.card ≤ 4
  · have hh : (S.card : ℝ) ≤ 4 := by exact_mod_cast hsmall
    exact hh.trans (hc N (by omega))
  have hne : P ≠ 0 := by intro hz; simp [PlaneCurvePointCount.degree, hz] at hD
  have hRF : Irreducible (rationalize P) :=
    ScalarIrreducibilityReflection.geometric_rational_irreducible P hne hgeo
  have hAbs : Irreducible (extend (rationalize P) : ℂ[X][X]) := by
    rw [ComplexProjectiveIrreducibility.rational_extension]
    exact (HomogenizationIrreducibilityReflection.geometric_iff_affine P hne).mp hgeo
  have hbox (z : ℤ × ℤ) (hz : z ∈ S) : z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N := by
    have hh := (PlaneCurvePointCount.mem_grid P N z).mp hz
    constructor
    · have hb : (z.1.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
      exact_mod_cast hb
    · have hb : (z.2.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
      exact_mod_cast hb
  obtain ⟨Q, hQ, hQabs, hassoc, hdegree, hheight, _hzero⟩ :=
    SmallHeightAssociatedPlanePresentation.exists_presentation P hRF hAbs N (by omega) S hbox
      (fun z hz ↦ ((PlaneCurvePointCount.mem_grid P N z).mp hz).2.2) (by rw [hD]; omega)
  have hQne : Q ≠ 0 := by
    intro hz
    apply hQ.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  have hQgeo : Geometric Q :=
    (HomogenizationIrreducibilityReflection.geometric_iff_affine Q hQne).mpr (by
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hQabs)
  have hQΔ : 0 < discriminant (coefficients Q) :=
    (ConicScalarInvariants.positive_discriminant_iff P Q hassoc).mp hΔ
  have hheight' : BivariateHeight.height Q ≤ BoundedPlaneInterpolation.heightBound 2 N := by
    simpa only [hD] using hheight
  have hheightC : BivariateHeight.height Q ≤ Cnat * N ^ κ :=
    hheight'.trans (BoundedPlaneInterpolation.heightBound_polynomial 2 N (by omega))
  have hheightN : BivariateHeight.height Q ≤ N ^ (κ + 1) := by
    calc
      _ ≤ Cnat * N ^ κ := hheightC
      _ ≤ N * N ^ κ := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hb := hq N (by omega) Q (hdegree.trans hD) hQgeo hQΔ hheightN
  rw [← SmallHeightAssociatedPlanePresentation.grid_eq_of_associated P Q hassoc N] at hb
  exact hb

theorem finite_population_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → 0 < discriminant (coefficients P) → ∀ S : Finset (ℤ × ℤ),
      (∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hcount⟩ := natural_count ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN P hD hgeo hΔ S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    have hh := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hh.1⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.1
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.2
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by exact_mod_cast card_le_card hsub
  exact hc.trans (hcount N hN P hD hgeo hΔ)

theorem polynomial_height_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 →
      Geometric P → 0 < discriminant (coefficients P) → ∀ B : ℕ, B ≤ N ^ K →
        ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let θ := ε / ((K : ℝ) + 1)
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hcancel : ((K : ℝ) + 1) * θ = ε := by dsimp only [θ]; field_simp
  have hbudget : (K : ℝ) * θ ≤ ε := by nlinarith
  obtain ⟨B₀, _hB₀, hcount⟩ := natural_count θ hθ
  have ht := ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop ((B₀ : ℝ) ^ θ))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ht
  refine ⟨max 2 N₁, by omega, ?_⟩
  intro N hN P hD hgeo hΔ B hBN
  by_cases hsmall : B < B₀
  · have hB : (B : ℤ) ≤ (B₀ : ℤ) := by exact_mod_cast hsmall.le
    have hsub : PlaneCurvePointCount.grid P B ⊆ PlaneCurvePointCount.grid P B₀ := by
      intro z hz
      have hh := (PlaneCurvePointCount.mem_grid P B z).mp hz
      exact (PlaneCurvePointCount.mem_grid P B₀ z).mpr ⟨hh.1.trans hB, hh.2.1.trans hB, hh.2.2⟩
    have hc : ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ ((PlaneCurvePointCount.grid P B₀).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact (hc.trans (hcount B₀ le_rfl P hD hgeo hΔ)).trans (hN₁ N (by omega))
  · have hc := hcount B (by omega) P hD hgeo hΔ
    have hBR : (B : ℝ) ≤ (N : ℝ) ^ K := by exact_mod_cast hBN
    have hpow : (B : ℝ) ^ θ ≤ (N : ℝ) ^ ε := by
      calc
        _ ≤ ((N : ℝ) ^ K) ^ θ := Real.rpow_le_rpow (Nat.cast_nonneg B) hBR hθ.le
        _ = (N : ℝ) ^ ((K : ℝ) * θ) := by rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N) K θ]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hbudget
    exact hc.trans hpow

end PaperP1.UnrestrictedHyperbolicConicCount
