module

public import PaperP1.Diophantine.NonGeometricBiformInput
public import PaperP1.Asymptotics.RationalSourceCurveFactors
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The ordinary conjugate-intersection input counts the actual non-geometric branch -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualNonGeometricFactorCount

open Finset Polynomial PaperP1.TwoKernelDeterminantBoxes PaperP1.ActualProjectivePairs
open PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover PaperP1.ConstructedClusterCurveData
open PaperP1.GeometricFactorSwap PaperP1.RationalBivariateIrreducibility PaperP1.BidegreeOneFibreCount
open PaperP1.IntegerFactorProjectiveCurve

theorem uniform_count (hNG : NonGeometricBiformInput.Input) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b →
      Irreducible (rationalize G) → ¬Geometric G → ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, s.1 1 ≠ 0 ∧ s.2 1 ≠ 0) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨K, _, hK⟩ := hNG a b ha hb
  obtain ⟨N₀, hN₀⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow K 0 ε hε
  refine ⟨N₀, ?_⟩
  intro N hN G hfirst hsecond hirr hnon S hprim hden hzero
  exact (hK G hfirst hsecond hirr hnon S hprim hden hzero).trans
    (by simpa only [Real.rpow_zero, mul_one] using hN₀ N hN)

theorem uniform_actual_count (hNG : NonGeometricBiformInput.Input) (Amax Bmax : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ κf : ℕ, ∀ Q : Finset Quad,
      ∀ B₀ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L T : ℝ, ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax Q B₀ B₁ L T F → ∀ c : Bool × Bool, ∀ G ∈ F c,
      ¬Geometric G → 0 < degreeX G → 0 < degreeY G →
        ((zeros G (FourProjectiveCharts.population c (Q.image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε := by
  choose Nd hNd using fun j : Fin (Amax + 1) × Fin (Bmax + 1) ↦
    uniform_count hNG (j.1.val + 1) (j.2.val + 1) (by omega) (by omega) ε hε
  refine ⟨univ.sup Nd, ?_⟩
  intro N hN κf Q B₀ B₁ L T F hcover c G hG hnon hfirst hsecond
  have hfactor := (hcover.factors c).2.1 G hG
  let j : Fin (Amax + 1) × Fin (Bmax + 1) :=
    (⟨degreeX G - 1, by have := hfactor.2.2.1; omega⟩,
      ⟨degreeY G - 1, by have := hfactor.2.2.2.1; omega⟩)
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans hN
  apply hNd j N hNj G (by dsimp [j]; omega) (by dsimp [j]; omega)
    (RationalSourceCurveFactors.local_cover_factors hcover c G hG) hnon
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.1, hpoint.2.1⟩
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩
  · intro p hp
    have hpoint := hcover.chart_points c p (mem_filter.mp hp).1
    exact (IntegerPairFactorCharts.projective_zero_iff G p.1 p.2 hpoint.2.2.1 hpoint.2.2.2.1).mpr
      (mem_filter.mp hp).2

theorem uniform_actual_minimum_count (hNG : NonGeometricBiformInput.Input) (Amax Bmax : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ κf : ℕ, ∀ Q : Finset Quad,
      ∀ B₀ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L T : ℝ, ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax Q B₀ B₁ L T F → ∀ c : Bool × Bool, ∀ G ∈ F c,
      ¬Geometric G → 0 < degreeX G → 0 < degreeY G →
        ((zeros G (FourProjectiveCharts.population c (Q.image (coordinates B₀ B₁)))).card : ℝ) ≤
          (N : ℝ) ^ ε * min L T := by
  obtain ⟨N₀, hN₀⟩ := uniform_actual_count hNG Amax Bmax ε hε
  refine ⟨N₀, ?_⟩
  intro N hN κf Q B₀ B₁ L T F hcover c G hG hnon hfirst hsecond
  have hh := hN₀ N hN κf Q B₀ B₁ L T F hcover c G hG hnon hfirst hsecond
  have hmin : 1 ≤ min L T := le_min hcover.horizontal_ge_one hcover.vertical_ge_one
  exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmin (Real.rpow_nonneg (Nat.cast_nonneg N) ε))

end PaperP1.ActualNonGeometricFactorCount
