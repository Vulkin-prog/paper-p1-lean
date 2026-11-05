module

public import PaperP1.Algebra.GeometricFactorSwap
public import PaperP1.Diophantine.BidegreeOneFibreCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The ordinary Heath-Brown biform input in its exact published scope

Primary source: D. R. Heath-Brown, Square-Free Values of n²+1,
arXiv:1010.6217v3, Lemma 2, printed page 9, with the proof in Section 6.
This is an ordinary proposition, used as an explicit argument in generic interfaces.
Its internal proof is GeometricBiformPointCount.full_input (P1-MATH-0361).
The coefficient norm is exactly the projective coefficient height by
ProjectiveFactorCoefficients.height_iff. The second pair has no height bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeathBrownBiformInput

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve
open PaperP1.GeometricFactorSwap PaperP1.BidegreeOneFibreCount

def Input : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b → Geometric G →
      ∀ L : ℝ, 1 ≤ L → ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) →
        (S.card : ℝ) ≤ K * L ^ (2 / (b : ℝ) + ε) * (height G : ℝ) ^ ε

end PaperP1.HeathBrownBiformInput
