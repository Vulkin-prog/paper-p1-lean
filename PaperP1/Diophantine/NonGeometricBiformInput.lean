module

public import PaperP1.Algebra.GeometricFactorSwap
public import PaperP1.Algebra.RationalBivariateIrreducibility
public import PaperP1.Diophantine.BidegreeOneFibreCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The separate ordinary conjugate-intersection input for non-geometric factors

This consequence is now proved internally by
ComplexProjectiveIrreducibility.nongeometric_input, with K(a,b)=8*a*b^2.
Its historical manuscript source is Heath-Brown, arXiv:1010.6217v3,
Section 4, printed page 8. The internal proof uses formal branches, scalar
coefficient descent, exact homogenization and resultant/primitive counting.
The proposition remains an explicit argument in existing APIs for compatibility.
The nonzero denominators retain the exact affine-chart scope. This is separate
from the still unproved geometric Heath-Brown Lemma 2 input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonGeometricBiformInput

open Polynomial PaperP1.BivariateDegrees PaperP1.IntegerFactorProjectiveCurve
open PaperP1.GeometricFactorSwap PaperP1.RationalBivariateIrreducibility PaperP1.BidegreeOneFibreCount

def Input : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X],
    degreeX G = a → degreeY G = b → Irreducible (rationalize G) → ¬Geometric G →
      ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, s.1 1 ≠ 0 ∧ s.2 1 ≠ 0) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
        (S.card : ℝ) ≤ K

end PaperP1.NonGeometricBiformInput
