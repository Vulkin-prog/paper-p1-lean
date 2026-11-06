module

public import PaperP1.Arithmetic.HyperellipticFiniteFieldPoints
public import PaperP1.Arithmetic.FiniteFieldPolynomialMultiplicityCount
public import PaperP1.Algebra.HyperellipticNormMultiplicity
public import Mathlib.Tactic.Positivity

/-! # An actual auxiliary function gives the literal quadratic-curve point bound

The auxiliary function, its nonzero property and tangent vanishings remain
explicit. This file does not assert that the required auxiliary exists.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticStepanovPointBound

open Finset Polynomial HyperellipticPolynomialAlgebra HyperellipticTangentDerivation
open HyperellipticFiniteFieldPoints DerivationPowerEvaluation

variable {F : Type*} [Field F] [Fintype F]

theorem good_cardinality_bound (p : ℕ) [CharP F p] (hp : p.Prime) (hchar : ringChar F ≠ 2)
    (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) (hz : z ≠ 0) (m : ℕ) (hm : m ≤ p)
    (hvanish : ∀ (x y : F) (hy : y ^ 2 = f.eval x), ∀ r < m,
      evaluation f x y hy (iter (tangent f) r z) = 0) :
    (2 * m) * (goodX f).card ≤ (QuadraticAlgebra.norm z).natDegree := by
  apply FiniteFieldPolynomialMultiplicityCount.cardinality
  intro x hx
  obtain ⟨y, hyn, hy⟩ := good_root f x hx
  exact HyperellipticNormMultiplicity.norm_root_multiplicity p hp (Ring.two_ne_zero hchar)
    f hodd x y hy hyn z hz m hm (hvanish x y hy)
    (hvanish x (-y) (by simpa only [neg_sq] using hy))

theorem multiplicative_bound (p : ℕ) [CharP F p] (hp : p.Prime) (hchar : ringChar F ≠ 2)
    (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) (hz : z ≠ 0) (m : ℕ) (hm : m ≤ p)
    (hvanish : ∀ (x y : F) (hy : y ^ 2 = f.eval x), ∀ r < m,
      evaluation f x y hy (iter (tangent f) r z) = 0) :
    m * (points f).card ≤ (QuadraticAlgebra.norm z).natDegree + m * f.natDegree := by
  have hg := good_cardinality_bound p hp hchar f hodd z hz m hm hvanish
  have hb := branch_card_le f (HyperellipticOddDegreeNorm.polynomial_ne_zero f hodd)
  rw [cardinality_decomposition hchar]
  calc
    _ = (2 * m) * (goodX f).card + m * (branchX f).card := by ring
    _ ≤ _ := Nat.add_le_add hg (Nat.mul_le_mul_left m hb)

theorem upper_bound (p : ℕ) [CharP F p] (hp : p.Prime) (hchar : ringChar F ≠ 2)
    (f : F[X]) (hodd : Odd f.natDegree) (z : CurveRing f) (hz : z ≠ 0)
    (m : ℕ) (hm0 : 0 < m) (hm : m ≤ p) (L : ℕ) (hL : (QuadraticAlgebra.norm z).natDegree ≤ L)
    (hvanish : ∀ (x y : F) (hy : y ^ 2 = f.eval x), ∀ r < m,
      evaluation f x y hy (iter (tangent f) r z) = 0) :
    ((points f).card : ℝ) ≤ (L : ℝ) / m + f.natDegree := by
  have hn := (multiplicative_bound p hp hchar f hodd z hz m hm hvanish).trans
    (Nat.add_le_add_right hL _)
  have hh : (m : ℝ) * ((points f).card : ℝ) ≤ (L : ℝ) + (m : ℝ) * f.natDegree := by
    exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  apply (mul_le_mul_iff_of_pos_right hmR).mp
  calc
    _ ≤ (L : ℝ) + (m : ℝ) * f.natDegree := by simpa only [mul_comm] using hh
    _ = ((L : ℝ) / m + f.natDegree) * m := by
      rw [add_mul, div_mul_cancel₀ _ hmR.ne']
      ring

end PaperP1.HyperellipticStepanovPointBound
