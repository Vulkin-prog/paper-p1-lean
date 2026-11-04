module

public import PaperP1.Asymptotics.ActualAuxiliaryFactorCover
public import PaperP1.Asymptotics.ActualClusterCoordinateBox

/-! # Actual occupied clusters have factor covers in their constructed lattice side boxes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConstructedClusterFactorCover

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition
open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform PaperP1.ActualProjectivePairs
open PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve PaperP1.IntegerPairFactorCover

theorem uniform_cluster_cover (Amax Bmax κw κ₀ κ₁ : ℕ) :
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
      let P := (cluster M X.D X.E k S).image (coordinates B₀ B₁)
      1 ≤ L₀ ∧ 1 ≤ T₀ ∧ ∃ T : Bool × Bool → Finset ℤ[X][X],
        (∀ c : Bool × Bool, (T c).card ≤ Amax + Bmax ∧
          (∀ G ∈ T c, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
            degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ κ' ∧ projective G ≠ 0 ∧
            (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ κ' : ℕ) : ℤ))) ∧
          (∀ p ∈ FourProjectiveCharts.population c P, ∃ G ∈ T c,
            MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
          (FourProjectiveCharts.population c P).card ≤
            ∑ G ∈ T c, (zeros G (FourProjectiveCharts.population c P)).card) ∧
        (∀ c : Bool × Bool, ∀ p ∈ FourProjectiveCharts.population c P,
          (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs ∧
          p.1 1 ≠ 0 ∧ p.2 1 ≠ 0 ∧ (∀ i, |(p.1 i : ℝ)| ≤ L₀) ∧ ∀ i, |(p.2 i : ℝ)| ≤ T₀) ∧
        (cluster M X.D X.E k S).card ≤
          ∑ c : Bool × Bool, ∑ G ∈ T c, (zeros G (FourProjectiveCharts.population c P)).card := by
  obtain ⟨κ', N₀, hcover⟩ := ActualAuxiliaryFactorCover.uniform_actual_cover Amax Bmax κw κ₀ κ₁
  refine ⟨κ', N₀, ?_⟩
  intro N hN ρ C δ X M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU h hMh S hS hprimitive hcluster a ha b hb w hw hH hzero
  have hprimcluster : ∀ p ∈ cluster M X.D X.E k S, Primitive p := by
    intro p hp
    exact hprimitive p ((mem_cluster M X.D X.E k S p).mp hp).1
  obtain ⟨T, hT, hsum⟩ := hcover N hN a ha b hb w hw hH A₀ B₀ A₁ B₁
    hD.right_inverse hD.left_inverse hU.right_inverse hU.left_inverse hD.basis_height hU.basis_height
    (cluster M X.D X.E k S) hprimcluster hzero
  have hlarge := ActualClusterCoordinateBox.nonempty_largest X A₀ B₀ A₁ B₁ hD hU h hMh S hS hprimitive hcluster
  refine ⟨hlarge.1, hlarge.2, T, hT, ?_, hsum⟩
  let P := (cluster M X.D X.E k S).image (coordinates B₀ B₁)
  have hPprimitive : ∀ p ∈ P, (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact coordinates_primitive A₀ B₀ A₁ B₁ hD.right_inverse hU.right_inverse q (hprimcluster q hq)
  have hPnonzero : ∀ p ∈ P, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    intro p hp
    exact ⟨UnimodularBinaryCoordinates.primitive_nonzero _ (hPprimitive p hp).1,
      UnimodularBinaryCoordinates.primitive_nonzero _ (hPprimitive p hp).2⟩
  intro c p hp
  have hprim := FourProjectiveCharts.population_primitive c P hPprimitive p hp
  have hden := FourProjectiveCharts.population_denominators c P hPnonzero p hp
  have hbox := ActualClusterCoordinateBox.chart_bounds X A₀ B₀ A₁ B₁ hD hU h hMh S hS c p hp
  exact ⟨hprim.1, hprim.2, hden.1, hden.2, hbox.1, hbox.2⟩

end PaperP1.ConstructedClusterFactorCover
