module

public import PaperP1.Algebra.P3HomogeneousIntegerInterpolation
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Actual homogeneous integer equations have coefficient-controlled derivative values at bounded-height points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HomogeneousDerivativeHeight

open MvPolynomial Finset P3HomogeneousCoefficientFamily

theorem evaluation_natAbs_bound (d A H : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ))
    (v : Fin 4 → ℤ) (hv : ∀ k, |v k| ≤ (H : ℤ)) :
    (eval v P).natAbs ≤ Fintype.card (Index d) * A * H ^ d := by
  classical
  have he := evaluation d (fun m : Index d ↦ P.coeff m.val) v
  rw [reconstruct d P hhom] at he
  have hb : |eval v P| ≤ ((Fintype.card (Index d) * A * H ^ d : ℕ) : ℤ) := by
    rw [he]
    calc
      _ ≤ ∑ m : Index d, |m.val.prod (fun k r ↦ v k ^ r) * P.coeff m.val| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Index d, (H : ℤ) ^ d * (A : ℤ) := by
        apply Finset.sum_le_sum
        intro m _
        rw [abs_mul]
        exact mul_le_mul (P3HomogeneousIntegerInterpolation.monomial_bound d m v H hv)
          (hcoef m.val) (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg H) d)
      _ = _ := by
        simp only [Finset.sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
        ring
  have hb' : ((eval v P).natAbs : ℤ) ≤ ((Fintype.card (Index d) * A * H ^ d : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs] using hb
  exact_mod_cast hb'

theorem derivative_coefficient_bound (d A : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) (k : Fin 4)
    (m : Fin 4 →₀ ℕ) : |(pderiv k P).coeff m| ≤ ((d * A : ℕ) : ℤ) := by
  classical
  rw [coeff_pderiv, abs_mul]
  by_cases hz : P.coeff (m + Finsupp.single k 1) = 0
  · rw [hz, abs_zero, zero_mul]
    positivity
  · have hd : (m + Finsupp.single k 1).degree = d := by
      have hh := hhom.degree_eq_sum_deg_support (mem_support_iff.mpr hz)
      simpa only [Finsupp.degree_apply] using hh.symm
    have hk : m k + 1 ≤ d := by
      have hh := Finsupp.le_degree k (m + Finsupp.single k 1)
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same, hd] using hh
    have hkZ : |(m k : ℤ) + 1| ≤ (d : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hk
    have hh := mul_le_mul (hcoef (m + Finsupp.single k 1)) hkZ
      (abs_nonneg _) (Nat.cast_nonneg A)
    simpa only [Nat.cast_mul, mul_comm] using hh

theorem derivative_value_bound (d A H : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ))
    (v : Fin 4 → ℤ) (hv : ∀ k, |v k| ≤ (H : ℤ)) (k : Fin 4) :
    (eval v (pderiv k P)).natAbs ≤ Fintype.card (Index (d - 1)) * (d * A) * H ^ (d - 1) :=
  evaluation_natAbs_bound (d - 1) (d * A) H (pderiv k P) hhom.pderiv
    (derivative_coefficient_bound d A P hhom hcoef k) v hv

end PaperP1.P3HomogeneousDerivativeHeight
