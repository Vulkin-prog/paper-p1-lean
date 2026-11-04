module

public import PaperP1.Asymptotics.ConstructedClusterFactorCover

/-! # Concrete factor-curve data for an actual cluster and its exact coordinate image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConstructedClusterCurveData

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform PaperP1.ActualProjectivePairs
open PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve PaperP1.IntegerPairFactorCover

structure LocalCover (N κ Amax Bmax : ℕ) (Q : Finset Quad)
    (B₀ B₁ : Matrix (Fin 2) (Fin 2) ℤ) (L T : ℝ) (F : Bool × Bool → Finset ℤ[X][X]) : Prop where
  horizontal_ge_one : 1 ≤ L
  vertical_ge_one : 1 ≤ T
  factors : let P := Q.image (coordinates B₀ B₁)
    ∀ c : Bool × Bool, (F c).card ≤ Amax + Bmax ∧
      (∀ G ∈ F c, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
        degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ κ ∧ projective G ≠ 0 ∧
        (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ))) ∧
      (∀ p ∈ FourProjectiveCharts.population c P, ∃ G ∈ F c,
        MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
      (FourProjectiveCharts.population c P).card ≤
        ∑ G ∈ F c, (zeros G (FourProjectiveCharts.population c P)).card
  chart_points : let P := Q.image (coordinates B₀ B₁)
    ∀ c : Bool × Bool, ∀ p ∈ FourProjectiveCharts.population c P,
      (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs ∧
      p.1 1 ≠ 0 ∧ p.2 1 ≠ 0 ∧ (∀ i, |(p.1 i : ℝ)| ≤ L) ∧ ∀ i, |(p.2 i : ℝ)| ≤ T
  count : let P := Q.image (coordinates B₀ B₁)
    Q.card ≤ ∑ c : Bool × Bool, ∑ G ∈ F c, (zeros G (FourProjectiveCharts.population c P)).card

theorem uniform_local_cover (Amax Bmax κw κ₀ κ₁ : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ C δ : ℝ, ∀ X : Box N ρ C δ, ∀ M k : ℕ,
      ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ, ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, (M : ℝ) * |(h : ℝ)| ≤ N → ∀ S : Finset Quad, SignedPopulation X h S →
      (∀ p ∈ S, Primitive p) → (cluster M X.D X.E k S).Nonempty →
      ∀ a ≤ Amax, ∀ b ≤ Bmax, ∀ w : Exponent a b → ℤ, biform a b w ≠ 0 →
      (∀ m n, |((biform a b w).coeff m).coeff n| ≤ ((N ^ κw : ℕ) : ℤ)) →
      (∀ p ∈ cluster M X.D X.E k S,
        MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2] (biform a b w) = 0) →
      ∃ F : Bool × Bool → Finset ℤ[X][X], LocalCover N κ' Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F := by
  obtain ⟨κ', N₀, hcover⟩ := ConstructedClusterFactorCover.uniform_cluster_cover Amax Bmax κw κ₀ κ₁
  refine ⟨κ', N₀, ?_⟩
  intro N hN ρ C δ X M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hMh S hS hprim hcluster a ha b hb w hw hH hzero
  obtain ⟨hL, hT, F, hfactors, hpoints, hcount⟩ := hcover N hN ρ C δ X M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hMh S hS hprim hcluster a ha b hb w hw hH hzero
  exact ⟨F, ⟨hL, hT, hfactors, hpoints, hcount⟩⟩

end PaperP1.ConstructedClusterCurveData
