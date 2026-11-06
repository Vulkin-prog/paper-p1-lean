module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.Field

/-! # Two power-algebraic field generators give a characteristic-independent dimension bound -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TwoPowerFieldDimension
open Polynomial Module IntermediateField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem integral_of_power (x : L) (D : ℕ) (hD : 0 < D) (a : K)
    (hpow : x ^ D = algebraMap K L a) : IsIntegral K x := by
  refine ⟨X ^ D - C a, monic_X_pow_sub_C a (Nat.ne_of_gt hD), ?_⟩
  change Polynomial.aeval x (X ^ D - C a) = 0
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hpow

theorem simple_finrank_le (x : L) (D : ℕ) (hD : 0 < D) (a : K)
    (hpow : x ^ D = algebraMap K L a) :
    Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) ≤ D := by
  have hx := integral_of_power x D hD a hpow
  rw [IntermediateField.adjoin.finrank hx]
  have hz : X ^ D - C a ≠ (0 : K[X]) := (monic_X_pow_sub_C a (Nat.ne_of_gt hD)).ne_zero
  have hr : Polynomial.aeval x (X ^ D - C a) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self]
  have hh := Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hr) hz
  simpa only [natDegree_X_pow_sub_C] using hh

theorem pair_finrank_le (x y : L) (D : ℕ) (hD : 0 < D) (a b : K)
    (hx : x ^ D = algebraMap K L a) (hy : y ^ D = algebraMap K L b) :
    Module.finrank K (IntermediateField.adjoin K ({x,y} : Set L)) ≤ D ^ 2 := by
  rw [← Set.singleton_union, IntermediateField.adjoin_union]
  have hh := Nat.mul_le_mul (simple_finrank_le x D hD a hx) (simple_finrank_le y D hD b hy)
  exact (IntermediateField.finrank_sup_le _ _).trans (by simpa only [pow_two] using hh)

theorem dimension_le (x y : L) (D : ℕ) (hD : 0 < D) (a b : K)
    (hx : x ^ D = algebraMap K L a) (hy : y ^ D = algebraMap K L b)
    (hgen : IntermediateField.adjoin K ({x,y} : Set L) = ⊤) :
    Module.finrank K L ≤ D ^ 2 := by
  have hh := pair_finrank_le x y D hD a b hx hy
  rw [hgen, IntermediateField.finrank_top'] at hh
  exact hh

theorem finiteDimensional (x y : L) (D : ℕ) (hD : 0 < D) (a b : K)
    (hx : x ^ D = algebraMap K L a) (hy : y ^ D = algebraMap K L b)
    (hgen : IntermediateField.adjoin K ({x,y} : Set L) = ⊤) :
    FiniteDimensional K L := by
  have hh := IntermediateField.finiteDimensional_adjoin_pair
    (integral_of_power x D hD a hx) (integral_of_power y D hD b hy)
  rw [hgen] at hh
  let : FiniteDimensional K (⊤ : IntermediateField K L) := hh
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end PaperP1.TwoPowerFieldDimension
