module

public import PaperP1.Algebra.OffsetCommonQuotientGraph
public import PaperP1.Algebra.BivariateGraphSpecialization
public import PaperP1.Diophantine.DisjointEquationGraphDescent

/-! # The actual common-quotient equations bound every admissible integral curve point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointCommonQuotientBound

open Polynomial Finset PaperP1.SelectedProportionalPairs

variable {F K ι : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]

theorem integral_point (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (good : Finset ι) (hgood : 3 ≤ good.card) (I : ι → Finset ℤ) (j : ι → ℤ) (b : ι → F)
    (hdisj : (good : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ good, (I ν).card = a)
    (hiB : ∀ ν ∈ good, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν ∈ good, (j ν).natAbs ≤ B)
    (hb : ∀ ν ∈ good, b ν ≠ 0) (x y t : K) (hx : Transcendental F x)
    (hcommon : ∀ ν ∈ good, algebraMap F K (b ν) * aeval x (FormalWordPolynomials.linearOver F (I ν)) =
      t * (y + (j ν : K))) (S T : Finset ℤ)
    (hiS : ∀ ν ∈ good, I ν ⊆ S) (hjT : ∀ ν ∈ good, j ν ∈ T)
    (X Y : ℤ) (hY : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : RingHom.ker (Polynomial.aevalAeval (R := F) x y).toRingHom ≤
      RingHom.ker (Polynomial.aevalAeval (R := F) (X : F) (Y : F)).toRingHom)
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ GridRationalGraphExclusion.bound a B := by
  obtain ⟨p, q, hq, hcop, hdegree, hgraph, hgrid⟩ := OffsetCommonQuotientGraph.exists_reduced_graph
    a ha good (by omega) I j b hdisj hcard hb x y t hx hcommon
  have heq := BivariateGraphSpecialization.point_equation x y (X : F) (Y : F) p q hgraph hpoint
  exact DisjointEquationGraphDescent.integral_point a B ha hB good I j hgood hdisj hcard hiB hjB S T
    hiS hjT p q hq hcop hdegree hgrid X Y hY heq hposS hposT hind hdirect

end PaperP1.DisjointCommonQuotientBound
