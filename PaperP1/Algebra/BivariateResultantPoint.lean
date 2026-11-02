module

public import PaperP1.Algebra.BivariateResultantNonzero
public import PaperP1.Algebra.IntegerPolynomialRootBound

/-! # A common large integer point forces divisibility once the resultant height is controlled -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateResultantPoint

open Polynomial PaperP1.BivariateDegrees

theorem common_point (f g : ℤ[X][X]) (m n : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hpos : m ≠ 0 ∨ n ≠ 0) (x y : ℤ) (hfx : f.evalEval x y = 0) (hgx : g.evalEval x y = 0) :
    (f.resultant g m n).eval x = 0 := by
  obtain ⟨p, q, _hp, _hq, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hpos
  have h := congrArg (Polynomial.evalEvalRingHom x y) hbez
  simp only [map_add, map_mul, coe_evalEvalRingHom, hfx, hgx, zero_mul, zero_add, evalEval_C] at h
  exact h.symm

theorem divides_of_large_point (C₀ P : ℤ[X][X]) (hC : Irreducible C₀) (hdegree : 0 < degreeY C₀)
    (x y : ℤ) (hCx : C₀.evalEval x y = 0) (hPx : P.evalEval x y = 0)
    (hx : PaperP1.integerPolynomialHeight (C₀.resultant P) < x.natAbs) : C₀ ∣ P := by
  by_contra hn
  have hne := BivariateResultantNonzero.nonzero_of_not_dvd C₀ P hC hdegree hn
  have he : (C₀.resultant P).IsRoot x :=
    common_point C₀ P C₀.natDegree P.natDegree le_rfl le_rfl
      (Or.inl (ne_of_gt hdegree)) x y hCx hPx
  exact (not_lt_of_ge (PaperP1.integerRoot_natAbs_le_height hne he)) hx

end PaperP1.BivariateResultantPoint
