module

public import PaperP1.Diophantine.GridRationalGraphExclusion
public import PaperP1.Algebra.IntegralInterpolationDescent

/-! # The actual grid bound over every characteristic-zero coefficient field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridRationalGraphDescent

open Polynomial PaperP1.SelectedProportionalPairs

theorem integral_point {F : Type*} [Field F] [CharZero F] (d B : ℕ) (hd : 0 < d) (hB : 1 ≤ B)
    (i j : Fin (2 * d + 1) → ℤ) (hinj : Function.Injective i)
    (hiB : ∀ t, (i t).natAbs ≤ B) (hjB : ∀ t, (j t).natAbs ≤ B)
    (S T : Finset ℤ) (hiS : ∀ t, i t ∈ S) (hjT : ∀ t, j t ∈ T)
    (p q : F[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = d)
    (hgrid : ∀ t, p.eval (-(i t : F)) = -(j t : F) * q.eval (-(i t : F)))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : F) = (Y : F) * q.eval (X : F))
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ GridRationalGraphExclusion.bound d B := by
  have hg (t) : p.eval ((-i t : ℤ) : F) = ((-j t : ℤ) : F) * q.eval ((-i t : ℤ) : F) := by
    simpa only [Int.cast_neg] using hgrid t
  obtain ⟨p₀, q₀, hq₀, hcop₀, hdeg₀, hpoints, _⟩ :=
    IntegralInterpolationDescent.exists_rational_descent d B hB (fun t ↦ -i t) (fun t ↦ -j t)
      (neg_injective.comp hinj) (fun t ↦ (Int.natAbs_neg _).trans_le (hiB t))
      (fun t ↦ (Int.natAbs_neg _).trans_le (hjB t)) p q hq0 hcop hdegree hg
  have hgrid₀ (t) : p₀.eval (-(i t : ℚ)) = -(j t : ℚ) * q₀.eval (-(i t : ℚ)) := by
    simpa only [Int.cast_neg] using (hpoints (-i t) (-j t)).mp (hg t)
  exact GridRationalGraphExclusion.integral_point d B hd hB i j hinj hiB hjB S T hiS hjT
    p₀ q₀ hq₀ hcop₀ hdeg₀ hgrid₀ X Y hcomparable ((hpoints X Y).mp hpoint) hposS hposT hind hdirect

end PaperP1.GridRationalGraphDescent
