module

public import PaperP1.Algebra.MvPolynomialHomogeneousBasis
public import PaperP1.Algebra.HomogeneousMonomialCount
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Exact dimensions of the actual ordinary homogeneous polynomial components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MvPolynomialHilbert

theorem piece_finite (F σ : Type*) [Field F] [Finite σ] (n : ℕ) :
    Module.Finite F (MvPolynomial.homogeneousSubmodule σ F n) := by
  have : Finite {d : σ →₀ ℕ // d.degree = n} := HomogeneousMonomialCount.exponent_finite σ n
  let : Fintype {d : σ →₀ ℕ // d.degree = n} := Fintype.ofFinite _
  exact Module.Finite.of_basis (MvPolynomialHomogeneousBasis.pieceBasis F σ n)

theorem piece_finrank (F σ : Type*) [Field F] (n : ℕ) :
    Module.finrank F (MvPolynomial.homogeneousSubmodule σ F n) = (Nat.card σ + n - 1).choose n := by
  rw [Module.finrank_eq_nat_card_basis (MvPolynomialHomogeneousBasis.pieceBasis F σ n)]
  exact HomogeneousMonomialCount.exponent_card σ n

theorem ternary_piece_finrank (F : Type*) [Field F] (n : ℕ) :
    Module.finrank F (MvPolynomial.homogeneousSubmodule (Fin 3) F n) = (n + 2).choose 2 := by
  rw [Module.finrank_eq_nat_card_basis (MvPolynomialHomogeneousBasis.pieceBasis F (Fin 3) n)]
  exact HomogeneousMonomialCount.ternary_exponent_card n

end PaperP1.MvPolynomialHilbert
