module

public import PaperP1.Algebra.ScaledSplitWordSquares
public import Mathlib.Tactic.LinearCombination

/-! # Actual functional squares on a line force a literal match of each selected root -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareLineMatching

open Finset Polynomial PaperP1.FormalWordPolynomials

theorem square_derivative_at_root {F : Type*} [Field F] (P : F[X]) (r : F)
    (hsquare : IsSquare P) (hroot : P.eval r = 0) : P.derivative.eval r = 0 := by
  obtain ⟨W, rfl⟩ := hsquare
  have hW : W.eval r = 0 := by simpa only [eval_mul, mul_self_eq_zero] using hroot
  simp [derivative_mul, hW]

theorem square_product_root {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (P Q : F[X])
    (hsep : P.Separable) (r : F) (hroot : P.eval r = 0)
    (hsquare : IsSquare (C c * P * Q)) : Q.eval r = 0 := by
  have hwhole : (C c * P * Q).eval r = 0 := by simp [hroot]
  have hder := square_derivative_at_root _ r hsquare hwhole
  have hroot₂ : P.eval₂ (RingHom.id F) r = 0 := by simpa only [eval₂_id] using hroot
  have hPder : P.derivative.eval r ≠ 0 := by
    simpa only [eval₂_id] using hsep.eval₂_derivative_ne_zero (RingHom.id F) hroot₂
  have hprod : c * P.derivative.eval r * Q.eval r = 0 := by
    simpa [derivative_mul, hroot] using hder
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc hPder)

def lineRestriction {F : Type*} [Field F] (c : F) (I J : Finset ℤ) (α β : F) : F[X] :=
  C c * linearOver F I * (linearOver F J).comp (C α * X + C β)

theorem matches_offset {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) (α β : F)
    (hsquare : IsSquare (lineRestriction c I J α β)) (i : ℤ) (hi : i ∈ I) :
    ∃ j ∈ J, β + (j : F) = α * (i : F) := by
  have hroot : (linearOver F I).eval (-(i : F)) = 0 := by
    simp only [linearOver, eval_prod, eval_add, eval_X, eval_C, prod_eq_zero_iff]
    exact ⟨i, hi, by ring⟩
  have hQ := square_product_root c hc (linearOver F I)
    ((linearOver F J).comp (C α * X + C β)) (ScaledSplitWordSquares.linear_separable I)
    (-(i : F)) hroot hsquare
  simp only [eval_comp, linearOver, eval_prod, eval_add, eval_mul, eval_C, eval_X,
    prod_eq_zero_iff] at hQ
  obtain ⟨j, hj, hz⟩ := hQ
  refine ⟨j, hj, ?_⟩
  linear_combination hz

theorem function_matches_offset {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) (α β : F)
    (hsquare : IsSquare (algebraMap F[X] (FractionRing F[X]) (lineRestriction c I J α β)))
    (i : ℤ) (hi : i ∈ I) : ∃ j ∈ J, β + (j : F) = α * (i : F) :=
  matches_offset c hc I J α β
    ((SquareInFractionField.square_reflect (R := F[X]) (K := FractionRing F[X]) _).mp hsquare) i hi

end PaperP1.SquareLineMatching
