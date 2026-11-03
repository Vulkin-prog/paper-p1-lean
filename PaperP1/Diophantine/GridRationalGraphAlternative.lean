module

public import PaperP1.Diophantine.GridRationalGraphExclusion
public import PaperP1.Algebra.LinearRationalGraph

/-! # A bounded offset grid forces a host bound or an actual affine graph

The affine alternative has no square-class independence hypothesis. It allows
the geometric applications to discharge the line case using their own scope.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridRationalGraphAlternative

open Polynomial

theorem integral_point (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (i j : Fin (2 * a + 1) → ℤ) (hinj : Function.Injective i)
    (hiB : ∀ t, (i t).natAbs ≤ B) (hjB : ∀ t, (j t).natAbs ≤ B)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ t, p.eval (-(i t : ℚ)) = -(j t : ℚ) * q.eval (-(i t : ℚ)))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ)) :
    X.natAbs ≤ GridRationalGraphExclusion.bound a B ∨
      ∃ α β : ℚ, ∀ x y : ℚ, (p.eval x = y * q.eval x ↔ y = α * x + β) := by
  have hneg : Function.Injective (fun t ↦ -i t) := neg_injective.comp hinj
  have hx : ∀ t, (-i t).natAbs ≤ B := fun t ↦ (Int.natAbs_neg _).trans_le (hiB t)
  have hy : ∀ t, (-j t).natAbs ≤ B := fun t ↦ (Int.natAbs_neg _).trans_le (hjB t)
  have hgrid' : ∀ t, p.eval ((-i t : ℤ) : ℚ) = ((-j t : ℤ) : ℚ) * q.eval ((-i t : ℤ) : ℚ) := by
    simpa only [Int.cast_neg] using hgrid
  by_cases hqpos : 0 < q.natDegree
  · exact Or.inl ((GridRationalGraphBound.integral_point a B hB (fun t ↦ -i t) (fun t ↦ -j t)
      hneg hx hy p q hq0 hcop hdegree hqpos hgrid' X Y hpoint).trans (le_max_left _ _))
  · have hqdeg : q.natDegree = 0 := by omega
    by_cases ha2 : 2 ≤ a
    · exact Or.inl ((GridPolynomialGraphBound.integral_point a B ha2 hB (fun t ↦ -i t) (fun t ↦ -j t)
        hneg hx hy p q hq0 hcop hdegree hqdeg hgrid' X Y hcomparable hpoint).trans (le_max_right _ _))
    · have hp : p.natDegree ≤ 1 := by have := le_max_left p.natDegree q.natDegree; omega
      exact Or.inr (LinearRationalGraph.exists_parameters p q hp hqdeg hq0)

end PaperP1.GridRationalGraphAlternative
