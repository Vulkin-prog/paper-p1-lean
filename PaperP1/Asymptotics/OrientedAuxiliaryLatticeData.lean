module

public import PaperP1.Arithmetic.DeterminantPositiveOrientation
public import PaperP1.Asymptotics.IdealSourceLatticeSums
public import PaperP1.Asymptotics.DeterminantBoxAuxiliary

/-! # Actual auxiliary curves, both reduced lattice families and ideal sums in one signed orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrientedAuxiliaryLatticeData

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
open PaperP1.DeterminantIntervalPartition PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale
open PaperP1.DeterminantPositiveOrientation PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
open PaperP1.QuadraticIntervalGrid

theorem uniform_oriented_data (ε η δ C ρ Kshift Aexp ζ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) (hgap : η + ζ / 2 < ε) :
    ∃ B Amax κw κ₀ κ₁ N₀ : ℕ, 0 < B ∧
      ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      ∀ X : Box N ρ C δ,
      let X' := orientedBox h X
      let M := horizontalScale N X.D X.E X.U X.V ζ
      let Sscale := Real.exp (logShape N X.D X.E X.U X.V)
      32 ≤ M ∧ 2 * M ≤ N ∧ (M : ℝ) * h.natAbs ≤ N ∧
      ∃ A₀ B₀ A₁ B₁ : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ T₀ T₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → HorizontalGridCoordinateData.Data X' κ₀ M k (A₀ k) (B₀ k) (L₀ k) (L₁ k)) ∧
        (∀ q : ℕ, q ≤ 4 * M → VerticalGridCoordinateData.Data X' κ₁ M q (A₁ q) (B₁ q) (T₀ q) (T₁ q)) ∧
        (∀ I : Finset ℕ, (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) →
          ((∑ k ∈ I, L₀ k) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * Sscale) + X.D + X.E)) ∧
          ((∑ k ∈ I, T₀ (grid M k)) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * Sscale) + X.U + X.V))) ∧
        ∀ S : Finset Quad, SignedPopulation X h S →
          let S' := orientedPopulation h S
          Population X' h.natAbs S' ∧ SignedPopulation X' (h.natAbs : ℤ) S' ∧
          S.card = ∑ k ∈ intervalIndices M, (cluster M X'.D X'.E k S').card ∧
          ∀ k ∈ intervalIndices M, (cluster M X'.D X'.E k S').Nonempty →
            ∃ a : ℕ, 0 < a ∧ a ≤ Amax ∧ ∃ w : Exponent a B → ℤ,
              biform a B w ≠ 0 ∧ (biform a B w).IsHomogeneous a ∧
              (∀ j, (forms a B w j).IsHomogeneous B) ∧
              (∀ m n, |((biform a B w).coeff m).coeff n| ≤ ((N ^ κw : ℕ) : ℤ)) ∧
              ∀ p ∈ cluster M X'.D X'.E k S',
                MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
                  ![(p.1.1 : ℤ), p.1.2] (biform a B w) = 0 := by
  obtain ⟨B, Amax, κw, NA, hB, haux⟩ :=
    DeterminantBoxAuxiliary.uniform_biforms δ C ρ Kshift Aexp ζ hδ hC hρ hρ₁ hζ hζsmall
  obtain ⟨κ₀, κ₁, NL, hlattices⟩ :=
    IdealSourceLatticeSums.uniform_ideal_sums ε η C ρ Kshift Aexp ζ hη hC hρ hζ hζsmall hgap
  refine ⟨B, Amax, κw, κ₀, κ₁, max NA NL, hB, ?_⟩
  intro N hN h hh hshift X
  let X' := orientedBox h X
  let M := horizontalScale N X.D X.E X.U X.V ζ
  let Sscale := Real.exp (logShape N X.D X.E X.U X.V)
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    have hz : (h.natAbs : ℤ) = |h| := Int.natCast_natAbs h
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun z : ℤ ↦ (z : ℝ)) hz
  have hshift' : (h.natAbs : ℝ) ≤ Kshift * (Real.log N) ^ Aexp := by simpa only [habs] using hshift
  have hl := hlattices N (by omega) h hh hshift δ X'
  simp only [X', scale_eq, shape_eq] at hl
  obtain ⟨hM, hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, hsums⟩ := hl
  have hMabs : (M : ℝ) * h.natAbs ≤ N := by simpa only [habs] using hMh
  refine ⟨hM, hMN, hMabs, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, ?_, ?_⟩
  · intro I hlow hupper
    have hs := hsums I hlow hupper
    constructor
    · simpa only [horizontal_cost_eq] using hs.1
    · simpa only [vertical_cost_eq] using hs.2
  · intro S hS
    let S' := orientedPopulation h S
    have hp := population X h S hS
    have ha := haux N (by omega) h.natAbs (Int.natAbs_pos.mpr hh) hshift' X' S' hp
    simp only [X', scale_eq] at ha
    refine ⟨hp, signed_population X h S hS, ?_, ha.2.2⟩
    exact (card_eq h S).symm.trans ha.2.1

end PaperP1.OrientedAuxiliaryLatticeData
