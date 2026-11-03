module

public import PaperP1.Combinatorics.DisjointOffsetGrid
public import PaperP1.Diophantine.DisjointEquationGraphBound
public import PaperP1.Algebra.IntegralInterpolationDescent

/-! # The disjoint-equation graph bound holds over every characteristic-zero coefficient field by actual rational descent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointEquationGraphDescent

open Polynomial PaperP1.SelectedProportionalPairs

theorem integral_point {F ι : Type*} [Field F] [CharZero F] (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (hA : 3 ≤ A.card)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a)
    (hiB : ∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν ∈ A, (j ν).natAbs ≤ B)
    (S T : Finset ℤ) (hiS : ∀ ν ∈ A, I ν ⊆ S) (hjT : ∀ ν ∈ A, j ν ∈ T)
    (p q : F[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ ν ∈ A, ∀ z ∈ I ν, p.eval (-(z : F)) = -(j ν : F) * q.eval (-(z : F)))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F))
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ GridRationalGraphExclusion.bound a B := by
  obtain ⟨x, y, hinj, hsel⟩ := DisjointOffsetGrid.select A I j a ha hA hdisj hcard
  have hx (t) : (x t).natAbs ≤ B := by
    obtain ⟨ν, hν, hx, _⟩ := hsel t
    exact hiB ν hν (x t) hx
  have hy (t) : (y t).natAbs ≤ B := by
    obtain ⟨ν, hν, _, hy⟩ := hsel t
    exact hy ▸ hjB ν hν
  have hg (t) : p.eval ((-x t : ℤ) : F) = ((-y t : ℤ) : F) * q.eval ((-x t : ℤ) : F) := by
    obtain ⟨ν, hν, hx, hy⟩ := hsel t
    simpa only [Int.cast_neg, hy] using hgrid ν hν (x t) hx
  obtain ⟨p₀, q₀, hq₀, hcop₀, hdeg₀, hpoints, _⟩ :=
    IntegralInterpolationDescent.exists_rational_descent a B hB (fun t ↦ -x t) (fun t ↦ -y t)
      (neg_injective.comp hinj) (fun t ↦ (Int.natAbs_neg _).trans_le (hx t))
      (fun t ↦ (Int.natAbs_neg _).trans_le (hy t)) p q hq0 hcop hdegree hg
  have hgrid₀ (ν) (hν : ν ∈ A) (z) (hz : z ∈ I ν) :
      p₀.eval (-(z : ℚ)) = -(j ν : ℚ) * q₀.eval (-(z : ℚ)) := by
    have hh : p.eval ((-z : ℤ) : F) = ((-j ν : ℤ) : F) * q.eval ((-z : ℤ) : F) := by
      simpa only [Int.cast_neg] using hgrid ν hν z hz
    simpa only [Int.cast_neg] using (hpoints (-z) (-j ν)).mp hh
  exact DisjointEquationGraphBound.integral_point a B ha hB A I j hA hdisj hcard hiB hjB S T hiS hjT
    p₀ q₀ hq₀ hcop₀ hdeg₀ hgrid₀ X Y hcomparable ((hpoints X Y).mp hpoint) hposS hposT hind hdirect

end PaperP1.DisjointEquationGraphDescent
