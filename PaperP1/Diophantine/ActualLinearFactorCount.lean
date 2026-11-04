module

public import PaperP1.Diophantine.LinearProjectiveFactor
public import PaperP1.Diophantine.LinearBivariateResultant
public import PaperP1.Diophantine.SingleResultantFibreCount

/-! # An unconditional uniform count on actual first-degree-one factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualLinearFactorCount

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.LinearBivariateCoefficients PaperP1.BidegreeOneFibreCount
open PaperP1.IntegerFactorProjectiveCurve

theorem uniform_count (ell k d κ : ℕ) (hd : 0 < d) (hdegree : 0 < k + d * ell)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : ℤ[X][X], Irreducible G → degreeX G = 1 → degreeY G = d →
      height G ≤ N ^ κ → ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ,
      (∀ i, (C i).IsHomogeneous k) → ∀ h : ℤ, h ≠ 0 → ∀ L T : ℝ, 0 ≤ L → 1 ≤ T →
      ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, BidegreeOneElimination.original C s.1 s.2 = h) →
      (∀ s ∈ S, (∀ i, |(s.1 i : ℝ)| ≤ L) ∧ ∀ i, |(s.2 i : ℝ)| ≤ T) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε * T := by
  obtain ⟨N₀, hN₀⟩ := SingleResultantFibreCount.actual_real_solutions_count ell k d (κ : ℝ) hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN G hG hfirst hsecond hheight C hC h hh L T hL hT S hprim hzero hsource hbox
  have hb := coefficient_degree_bounds G
  have hR := LinearBivariateResultant.actual_resultant_ne_zero G hG hfirst (by omega)
  have hcoeff := LinearBivariateCoefficients.coefficient_height G
  have hfc : ∀ j, (((firstCoefficient G).coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ (κ : ℝ) := by
    intro j
    have hj := (hcoeff.1 j).trans hheight
    simpa only [Real.rpow_natCast, Nat.cast_pow] using (show (((firstCoefficient G).coeff j).natAbs : ℝ) ≤ ((N ^ κ : ℕ) : ℝ) by exact_mod_cast hj)
  have hgc : ∀ j, (((secondCoefficient G).coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ (κ : ℝ) := by
    intro j
    have hj := (hcoeff.2 j).trans hheight
    simpa only [Real.rpow_natCast, Nat.cast_pow] using (show (((secondCoefficient G).coeff j).natAbs : ℝ) ≤ ((N ^ κ : ℕ) : ℝ) by exact_mod_cast hj)
  have hcount := hN₀ N hN (firstCoefficient G) (secondCoefficient G) (by simpa only [hsecond] using hb.1)
    (by simpa only [hsecond] using hb.2) (by simpa only [hsecond] using hR) hfc hgc C hC h hh L T hL hT
  have hsub : S ⊆ BidegreeOneCurveCount.realSolutions C (firstCoefficient G) (secondCoefficient G) d h L T := by
    intro s hs
    apply (BidegreeOneCurveCount.mem_realSolutions _ _ _ _ _ _ _ hL (by linarith) s).mpr
    refine ⟨(hbox s hs).1, (hbox s hs).2, (hprim s hs).1, (hprim s hs).2, ?_, hsource s hs⟩
    have hz := (LinearProjectiveFactor.evaluation_linear G hfirst s.1 s.2).symm.trans (hzero s hs)
    simpa only [hsecond] using hz
  exact (show (S.card : ℝ) ≤ ((BidegreeOneCurveCount.realSolutions C (firstCoefficient G) (secondCoefficient G) d h L T).card : ℝ) by exact_mod_cast card_le_card hsub).trans hcount

end PaperP1.ActualLinearFactorCount
