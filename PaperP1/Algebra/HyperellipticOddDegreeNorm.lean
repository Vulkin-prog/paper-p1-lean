module

public import PaperP1.Algebra.HyperellipticPolynomialAlgebra
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Lean.Elab.Tactic.Omega

/-! # Odd degree makes the actual quadratic polynomial norm detect nonzero functions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticOddDegreeNorm

open Polynomial HyperellipticPolynomialAlgebra
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

theorem polynomial_ne_zero (f : F[X]) (hodd : Odd f.natDegree) : f ≠ 0 := by
  intro hz
  rw [hz, natDegree_zero] at hodd
  obtain ⟨n, hn⟩ := hodd
  omega

theorem unequal_square_degrees (f A B : F[X]) (hodd : Odd f.natDegree) (hB : B ≠ 0) :
    (A ^ 2).natDegree ≠ (f * B ^ 2).natDegree := by
  rw [natDegree_pow, natDegree_mul (polynomial_ne_zero f hodd) (pow_ne_zero 2 hB), natDegree_pow]
  obtain ⟨g, hg⟩ := hodd
  omega

theorem norm_eq_zero_iff (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) :
    QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [norm_formula, sub_eq_zero] at hz
    by_cases hB : z.im = 0
    · have hA : z.re = 0 := by
        rw [hB, zero_pow (by decide : 2 ≠ 0), mul_zero] at hz
        exact sq_eq_zero_iff.mp hz
      exact (zero_iff f z).mpr ⟨hA, hB⟩
    · exact False.elim (unequal_square_degrees f z.re z.im hodd hB (congrArg natDegree hz))
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

theorem norm_ne_zero (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) (hz : z ≠ 0) :
    QuadraticAlgebra.norm z ≠ 0 := (norm_eq_zero_iff f hodd z).not.mpr hz

theorem norm_degree_mul (f : F[X]) (z w : CurveRing f) :
    (QuadraticAlgebra.norm (z * w)).degree =
      (QuadraticAlgebra.norm z).degree + (QuadraticAlgebra.norm w).degree := by
  rw [map_mul, degree_mul]

theorem norm_natDegree_mul (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f)
    (hz : z ≠ 0) (hw : w ≠ 0) :
    (QuadraticAlgebra.norm (z * w)).natDegree =
      (QuadraticAlgebra.norm z).natDegree + (QuadraticAlgebra.norm w).natDegree := by
  rw [map_mul, natDegree_mul (norm_ne_zero f hodd z hz) (norm_ne_zero f hodd w hw)]

theorem product_ne_zero (f : F[X]) (hodd : Odd f.natDegree) (z w : CurveRing f)
    (hz : z ≠ 0) (hw : w ≠ 0) : z * w ≠ 0 := by
  intro hzero
  have hh := congrArg (fun u : CurveRing f ↦ QuadraticAlgebra.norm u) hzero
  rw [map_mul, QuadraticAlgebra.norm_zero] at hh
  exact mul_ne_zero (norm_ne_zero f hodd z hz) (norm_ne_zero f hodd w hw) hh

theorem norm_natDegree (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) :
    (QuadraticAlgebra.norm z).natDegree =
      if z.im = 0 then 2 * z.re.natDegree else
        max (2 * z.re.natDegree) (f.natDegree + 2 * z.im.natDegree) := by
  rw [norm_formula]
  by_cases hB : z.im = 0
  · rw [ite_eq_left hB]
    simp only [hB, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, natDegree_pow]
  · rw [ite_eq_right hB]
    have hAdeg : (z.re ^ 2).natDegree = 2 * z.re.natDegree := natDegree_pow _ _
    have hBdeg : (f * z.im ^ 2).natDegree = f.natDegree + 2 * z.im.natDegree := by
      rw [natDegree_mul (polynomial_ne_zero f hodd) (pow_ne_zero 2 hB), natDegree_pow]
    rcases lt_or_gt_of_ne (unequal_square_degrees f z.re z.im hodd hB) with hlt | hgt
    · rw [natDegree_sub_eq_right_of_natDegree_lt hlt, hBdeg]
      rw [hAdeg, hBdeg] at hlt
      exact (max_eq_right (Nat.le_of_lt hlt)).symm
    · rw [natDegree_sub_eq_left_of_natDegree_lt hgt, hAdeg]
      rw [hAdeg, hBdeg] at hgt
      exact (max_eq_left (Nat.le_of_lt hgt)).symm

end PaperP1.HyperellipticOddDegreeNorm
