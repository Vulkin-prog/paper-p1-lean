module

public import PaperP1.Arithmetic.IntegerCurveRationalization
public import PaperP1.Algebra.ManyPointsScalarDescent
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Extracting an actual integer factor associated to a rational prime divisor

The factor divides the original integer polynomial, so the existing integer
factor-height theorem can be applied after a bounded interpolation step.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalAssociatedIntegerFactor

open Polynomial

theorem exists_factor_dvd_map {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (P : R) (hP : P ≠ 0) (q : S) (hq : Prime q) (hdiv : q ∣ φ P) :
    ∃ C : R, Irreducible C ∧ C ∣ P ∧ q ∣ φ C := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hP rfl).elim
  | unit u hu => exact (hq.not_isUnit (isUnit_of_dvd_unit hdiv (hu.map φ))).elim
  | mul a i ha hi ih =>
    rw [map_mul] at hdiv
    rcases hq.dvd_mul.mp hdiv with hleft | hright
    · exact ⟨i, hi, ⟨a, rfl⟩, hleft⟩
    · obtain ⟨C, hC, hCa, hqC⟩ := ih ha hright
      exact ⟨C, hC, dvd_mul_of_dvd_right hCa i, hqC⟩

theorem exists_integer_factor (F : ℚ[X][X]) (hF : Irreducible F)
    (Q : ℤ[X][X]) (hQ : Q ≠ 0)
    (hdiv : F ∣ IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ) Q) :
    ∃ C : ℤ[X][X], Irreducible C ∧ C ∣ Q ∧
      Associated F (IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ) C) := by
  let φ := IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ)
  obtain ⟨C, hC, hCQ, hFC⟩ := exists_factor_dvd_map φ Q hQ F
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF) hdiv
  have hinj : Function.Injective φ :=
    IntegerCurveRationalization.coefficientMap_injective _ (Int.cast_injective (α := ℚ))
  have hne : φ C ≠ 0 := by
    intro hz
    exact hC.ne_zero (hinj (hz.trans (map_zero φ).symm))
  have hdegree : 0 < BivariateTotalDegree.totalDegree C := by
    by_contra h
    have hz : PlaneCurvePointCount.degree (φ C) = 0 := by
      rw [IntegerCurveRationalization.degree_coefficientMap _ (Int.cast_injective (α := ℚ))]
      exact Nat.eq_zero_of_not_pos h
    have hu := ManyPointsScalarDescent.unit_of_degree_zero (φ C) hne hz
    exact hF.not_isUnit (isUnit_of_dvd_unit hFC hu)
  have hmap := IntegerCurveRationalization.rational_irreducible C hC hdegree
  exact ⟨C, hC, hCQ, hF.associated_of_dvd hmap hFC⟩

end PaperP1.RationalAssociatedIntegerFactor
