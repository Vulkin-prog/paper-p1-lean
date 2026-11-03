module

public import PaperP1.Algebra.AffineCurveFunctionField
public import PaperP1.Diophantine.DisjointCommonQuotientBound

/-! # The common-quotient bound at actual integral points of an irreducible plane curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveCommonQuotientBound

open Polynomial Finset PaperP1.AffineCurveFunctionField PaperP1.SelectedProportionalPairs

variable {F ι : Type*} [Field F] [CharZero F]

theorem integral_point (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (good : Finset ι) (hgood : 3 ≤ good.card) (I : ι → Finset ℤ) (j : ι → ℤ) (b : ι → F)
    (hdisj : (good : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ good, (I ν).card = a)
    (hiB : ∀ ν ∈ good, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν ∈ good, (j ν).natAbs ≤ B)
    (hb : ∀ ν ∈ good, b ν ≠ 0) (t : FunctionField C₀)
    (hcommon : ∀ ν ∈ good,
      algebraMap F (FunctionField C₀) (b ν) * aeval (firstCoordinate C₀) (FormalWordPolynomials.linearOver F (I ν)) =
        t * (secondCoordinate C₀ + (j ν : FunctionField C₀)))
    (S T : Finset ℤ) (hiS : ∀ ν ∈ good, I ν ⊆ S) (hjT : ∀ ν ∈ good, j ν ∈ T)
    (X Y : ℤ) (hY : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : Polynomial.aevalAeval (X : F) (Y : F) C₀ = 0)
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ GridRationalGraphExclusion.bound a B :=
  DisjointCommonQuotientBound.integral_point a B ha hB good hgood I j b hdisj hcard hiB hjB hb
    (firstCoordinate C₀) (secondCoordinate C₀) t (first_transcendental C₀ hdegree) hcommon S T hiS hjT X Y hY
    (point_kernel_le C₀ (X : F) (Y : F) hpoint) hposS hposT hind hdirect

end PaperP1.CurveCommonQuotientBound
