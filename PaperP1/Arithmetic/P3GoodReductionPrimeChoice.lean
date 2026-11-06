module

public import PaperP1.Arithmetic.P3UniversalGoodReduction
public import Mathlib.NumberTheory.Bertrand

/-! # A geometrically irreducible reduction exists at a prime of polynomial coefficient height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GoodReductionPrimeChoice

open MvPolynomial

theorem prime_above_certificate (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z) (B : ℕ) (hB : 0 < B) (hbound : z.natAbs ≤ B) :
    ∃ p : ℕ, ∃ hp : p.Prime, B < p ∧ p ≤ 2 * B ∧
      P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  obtain ⟨p, hp, hBp, hpB⟩ := Nat.exists_prime_lt_and_le_two_mul B hB.ne'
  refine ⟨p, hp, hBp, hpB, P3UniversalGoodReduction.geometric_reduction P z hcert p hp ?_⟩
  intro hdiv
  have hh := Int.natAbs_le_of_dvd_ne_zero hdiv hz
  simp only [Int.natAbs_natCast] at hh
  omega

theorem polynomial_prime_bound (d : ℕ) :
    ∃ T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A → ∀ P : MvPolynomial (Fin 4) ℤ,
      P.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) →
      (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∃ p : ℕ, ∃ hp : p.Prime, T * A ^ N < p ∧ p ≤ 2 * T * A ^ N ∧
        P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  obtain ⟨T, N, hT, hcert⟩ := P3UniversalGoodReduction.bounded_certificate d
  refine ⟨T, N, hT, ?_⟩
  intro A hA P hP hgeom hcoef
  obtain ⟨z, hz, hbound, hgood⟩ := hcert A hA P hP hgeom hcoef
  obtain ⟨p, hp, hBp, hpB, hred⟩ := prime_above_certificate P z hz hgood (T * A ^ N)
    (Nat.mul_pos hT (Nat.pow_pos hA)) hbound
  exact ⟨p, hp, hBp, by simpa only [Nat.mul_assoc] using hpB, hred⟩

end PaperP1.P3GoodReductionPrimeChoice
