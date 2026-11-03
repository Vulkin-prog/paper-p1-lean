module

public import PaperP1.Algebra.StandardVeronesePieceBasis
public import PaperP1.Algebra.HomogeneousMonomialCount
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Exact dimensions of the native standard Veronese pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardVeroneseHilbert

open PaperP1.SourceVeroneseGrading

theorem piece_finite (F : Type*) [Field F] (D n : ℕ) : Module.Finite F (nativePiece F D n) := by
  have : Finite {d : Fin 3 →₀ ℕ // d.degree = n * D} :=
    HomogeneousMonomialCount.exponent_finite (Fin 3) _
  let : Fintype {d : Fin 3 →₀ ℕ // d.degree = n * D} := Fintype.ofFinite _
  exact Module.Finite.of_basis (StandardVeronesePieceBasis.pieceBasis F D n)

theorem piece_finrank (F : Type*) [Field F] (D n : ℕ) :
    Module.finrank F (nativePiece F D n) = (n * D + 2).choose 2 := by
  rw [Module.finrank_eq_nat_card_basis (StandardVeronesePieceBasis.pieceBasis F D n)]
  exact HomogeneousMonomialCount.ternary_exponent_card _

end PaperP1.StandardVeroneseHilbert
