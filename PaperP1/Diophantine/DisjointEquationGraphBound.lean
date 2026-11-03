module

public import PaperP1.Combinatorics.DisjointOffsetGrid
public import PaperP1.Diophantine.GridRationalGraphExclusion

/-! # Three actual disjoint equation-root families give the grid-uniform arithmetic graph bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointEquationGraphBound

open Polynomial PaperP1.SelectedProportionalPairs

theorem integral_point {ι : Type*} (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (hA : 3 ≤ A.card)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a)
    (hiB : ∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) (hjB : ∀ ν ∈ A, (j ν).natAbs ≤ B)
    (S T : Finset ℤ) (hiS : ∀ ν ∈ A, I ν ⊆ S) (hjT : ∀ ν ∈ A, j ν ∈ T)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ ν ∈ A, ∀ z ∈ I ν, p.eval (-(z : ℚ)) = -(j ν : ℚ) * q.eval (-(z : ℚ)))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ))
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
  have hxs (t) : x t ∈ S := by
    obtain ⟨ν, hν, hx, _⟩ := hsel t
    exact hiS ν hν hx
  have hyt (t) : y t ∈ T := by
    obtain ⟨ν, hν, _, hy⟩ := hsel t
    exact hy ▸ hjT ν hν
  have hg (t) : p.eval (-(x t : ℚ)) = -(y t : ℚ) * q.eval (-(x t : ℚ)) := by
    obtain ⟨ν, hν, hx, hy⟩ := hsel t
    exact hy ▸ hgrid ν hν (x t) hx
  exact GridRationalGraphExclusion.integral_point a B ha hB x y hinj hx hy S T hxs hyt
    p q hq0 hcop hdegree hg X Y hcomparable hpoint hposS hposT hind hdirect

end PaperP1.DisjointEquationGraphBound
