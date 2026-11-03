module

public import PaperP1.Algebra.UniformRationalInterpolation
public import PaperP1.Diophantine.IntegralPolynomialGraphBound

/-! # Grid-uniform exclusion of large comparable integral points on a polynomial graph of degree at least two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridPolynomialGraphBound

open Polynomial PaperP1.IntegralRationalInterpolation

theorem integral_point (a B : ℕ) (ha : 2 ≤ a) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hqdeg : q.natDegree = 0) (hgrid : ∀ j, p.eval (x j : ℚ) = (y j : ℚ) * q.eval (x j : ℚ))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ)) :
    X.natAbs ≤ (a + 2) * heightBound a B := by
  obtain ⟨P, Q, _, _, _, hpc, hqc, _, _, δ, hδ, hpδ, hqδ⟩ :=
    UniformRationalInterpolation.exists_integral_presentation a B hB x y hinj hx hy p q hq0 hcop hdegree hgrid
  have hpdegree : p.natDegree = a := by simpa only [hqdeg, max_zero] using hdegree
  have hPdegree : P.natDegree = a := (UniformRationalInterpolation.scalar_degree_eq P p δ hδ hpδ).trans hpdegree
  have hQdegree : Q.natDegree = 0 := (UniformRationalInterpolation.scalar_degree_eq Q q δ hδ hqδ).trans hqdeg
  have hpointZ := UniformRationalInterpolation.integral_point_of_scalar P Q p q δ hpδ hqδ X Y hpoint
  have heval : Q.eval X = Q.coeff 0 :=
    (congrArg (Polynomial.eval X) (eq_C_of_natDegree_eq_zero hQdegree)).trans (eval_C)
  rw [heval] at hpointZ
  exact IntegralPolynomialGraphBound.abscissa_bound a (heightBound a B) ha P hPdegree hpc
    (Q.coeff 0) X Y (hqc 0) hcomparable hpointZ

end PaperP1.GridPolynomialGraphBound
