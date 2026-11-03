module

public import PaperP1.Algebra.IntegralPolynomialValueBound
public import PaperP1.Diophantine.ResultantHeight

/-! # Explicit integral-point bounds for a reduced rational graph with nonconstant denominator -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralRationalGraphBound

open Polynomial

theorem actual_resultant_ne_zero (P Q : ℤ[X])
    (hcop : IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ))) :
    P.resultant Q P.natDegree Q.natDegree ≠ 0 := by
  have hdp : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective P
  have hdq : (Q.map (Int.castRingHom ℚ)).natDegree = Q.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective Q
  have hres := Polynomial.resultant_ne_zero (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) hcop
  intro hz
  rw [hdp, hdq, Polynomial.resultant_map_map, hz, map_zero] at hres
  exact hres rfl

theorem denominator_dvd_resultant (P Q : ℤ[X]) (hQ : 0 < Q.natDegree) (x y : ℤ)
    (hpoint : P.eval x = y * Q.eval x) : Q.eval x ∣ P.resultant Q P.natDegree Q.natDegree :=
  ResultantDivisibility.dvd_resultant_of_dvd_evaluations P Q _ _ le_rfl le_rfl
    (Or.inr hQ.ne') x (Q.eval x) ⟨y, by rw [hpoint, mul_comm]⟩ (dvd_refl _)

theorem denominator_value_bound (P Q : ℤ[X]) (hQ : 0 < Q.natDegree) (x y : ℤ)
    (hcop : IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)))
    (hpoint : P.eval x = y * Q.eval x) :
    (Q.eval x).natAbs ≤ (P.resultant Q P.natDegree Q.natDegree).natAbs :=
  Int.natAbs_le_of_dvd_ne_zero (denominator_dvd_resultant P Q hQ x y hpoint) (actual_resultant_ne_zero P Q hcop)

theorem abscissa_bound (a M : ℕ) (hM : 1 ≤ M) (P Q : ℤ[X])
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ a) (hQpos : 0 < Q.natDegree)
    (hpc : ∀ n, (P.coeff n).natAbs ≤ M) (hqc : ∀ n, (Q.coeff n).natAbs ≤ M)
    (hcop : IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)))
    (x y : ℤ) (hpoint : P.eval x = y * Q.eval x) :
    x.natAbs ≤ M + (2 * a).factorial * M ^ (2 * a) := by
  have hdeg : P.natDegree + Q.natDegree ≤ 2 * a := by omega
  have hval := (denominator_value_bound P Q hQpos x y hcop hpoint).trans
    (ResultantHeight.resultant_bound P Q P.natDegree Q.natDegree M hpc hqc)
  have hval' : (Q.eval x).natAbs ≤ (2 * a).factorial * M ^ (2 * a) :=
    hval.trans (Nat.mul_le_mul (Nat.factorial_le hdeg) (Nat.pow_le_pow_right hM hdeg))
  exact IntegralPolynomialValueBound.bounded_value Q hQpos M _ x hqc hval'

end PaperP1.IntegralRationalGraphBound
