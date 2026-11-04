module

public import PaperP1.Diophantine.FourChartEquations
public import PaperP1.Asymptotics.IntegerPairFactorCover

/-! # Actual uniformly bounded factor curves after all four projective chart changes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourChartFactorCover

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.FourProjectiveCharts PaperP1.FourChartEquations PaperP1.BiformCoordinateEquation
open PaperP1.IntegerFactorProjectiveCurve PaperP1.IntegerPairFactorCover

theorem uniform_factor_covers (Amax Bmax κ : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ a ≤ Amax, ∀ b ≤ Bmax,
      ∀ F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ,
      (∀ i, (F i).IsHomogeneous b) → F ≠ 0 →
      (∀ i m, ((F i).coeff m).natAbs ≤ N ^ κ) →
      ∀ S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
      (∀ p ∈ S, (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs) →
      (∀ p ∈ S, BidegreeOneElimination.original F p.1 p.2 = 0) →
      ∃ T : Bool × Bool → Finset ℤ[X][X],
        (∀ c : Bool × Bool, (T c).card ≤ Amax + Bmax ∧
          (∀ G ∈ T c, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
            degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ κ' ∧ projective G ≠ 0 ∧
            (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ κ' : ℕ) : ℤ))) ∧
          (∀ p ∈ population c S, ∃ G ∈ T c,
            MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
          (population c S).card ≤ ∑ G ∈ T c, (zeros G (population c S)).card) ∧
        S.card ≤ ∑ c : Bool × Bool, ∑ G ∈ T c, (zeros G (population c S)).card := by
  classical
  obtain ⟨κ₁, N₁, hcharts⟩ := uniform_four_chart_reduction Amax Bmax κ
  obtain ⟨N₂, hcover⟩ := IntegerPairFactorCover.uniform_bounded_projective_cover Amax Bmax κ₁
  refine ⟨κ₁ + 1, max N₁ N₂, ?_⟩
  intro N hN a ha b hb F hF hF0 hH S hprimitive hzero
  obtain ⟨hpartition, hc⟩ := hcharts N (by omega) a ha b hb F hF hF0 hH S hprimitive hzero
  have hlocal (c : Bool × Bool) :
      ∃ T : Finset ℤ[X][X], T.card ≤ Amax + Bmax ∧
        (∀ G ∈ T, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
          degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ (κ₁ + 1) ∧ projective G ≠ 0 ∧
          (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ (κ₁ + 1) : ℕ) : ℤ))) ∧
        (∀ p ∈ population c S, ∃ G ∈ T,
          MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
        (population c S).card ≤ ∑ G ∈ T, (zeros G (population c S)).card := by
    obtain ⟨hc0, _, _, hcH, hpoints⟩ := hc c
    have hdenom : ∀ p ∈ population c S, p.1 1 ≠ 0 ∧ p.2 1 ≠ 0 :=
      fun p hp ↦ ⟨(hpoints p hp).1, (hpoints p hp).2.1⟩
    have hz : ∀ p ∈ population c S,
        MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1
          (equation (b := b) (family (b := b) c F)) = 0 := fun p hp ↦ (hpoints p hp).2.2.2.2
    obtain ⟨G, hG0, hGx, hGy, hGH, hGz⟩ := IntegerPairFactorCover.affine_of_biform a b (N ^ κ₁)
      (weights (b := b) (family (b := b) c F)) hc0 hcH (population c S) hdenom hz
    obtain ⟨T, hT, hfactors, hactual, hsum⟩ := hcover N (by omega) G hG0
      (hGx.trans ha) (hGy.trans hb) hGH (population c S) hdenom hGz
    refine ⟨T, hT, ?_, hactual, hsum⟩
    intro P hP
    obtain ⟨hirr, _, hpos, hpx, hpy, hheight, hnonzero, hcoeff⟩ := hfactors P hP
    exact ⟨hirr, hpos, hpx, hpy, hheight, hnonzero, hcoeff⟩
  choose T hT using hlocal
  refine ⟨T, hT, ?_⟩
  rw [hpartition]
  exact sum_le_sum (fun c _ ↦ (hT c).2.2.2)

end PaperP1.FourChartFactorCover
