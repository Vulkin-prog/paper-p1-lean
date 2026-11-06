module

public import PaperP1.Algebra.HomogeneousLinearForm
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Tactic.Ring

/-! # The actual integer-coefficient Hessian of a homogeneous quadratic polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousQuadraticHessian

open MvPolynomial Finset
open scoped Classical

variable {R S σ : Type*} [CommRing R] [CommRing S]

def entry (P : MvPolynomial σ R) (i j : σ) : R :=
  (pderiv j (pderiv i P)).coeff 0

theorem symmetric (P : MvPolynomial σ R) (i j : σ) : entry P i j = entry P j i := by
  rw [entry, pderiv_comm, entry]

theorem coefficient (P : MvPolynomial σ R) (i j : σ) :
    entry P i j = (pderiv i P).coeff (Finsupp.single j 1) := by
  simp only [entry, coeff_pderiv, zero_add, Finsupp.zero_apply, Nat.cast_zero,
    zero_add, mul_one]

theorem map_entry (φ : R →+* S) (P : MvPolynomial σ R) (i j : σ) :
    entry (map φ P) i j = φ (entry P i j) := by
  simp only [entry, pderiv_map, coeff_map]

theorem coefficient_formula (P : MvPolynomial σ R) (i j : σ) :
    entry P i j = P.coeff (Finsupp.single i 1 + Finsupp.single j 1) *
      (if i = j then 2 else 1) := by
  rw [coefficient, coeff_pderiv, add_comm (Finsupp.single j 1)]
  by_cases hij : i = j
  · subst j
    simp only [Finsupp.single_eq_same, Nat.cast_one, ite_true]
    ring
  · simp only [Finsupp.single_eq_of_ne hij, Nat.cast_zero, zero_add, ite_eq_right hij, mul_one]

variable [Fintype σ]

theorem gradient (P : MvPolynomial σ R) (hP : P.IsHomogeneous 2) (i : σ) :
    pderiv i P = ∑ j, C (entry P i j) * X j := by
  have hh : (pderiv i P).IsHomogeneous 1 := hP.pderiv
  simpa only [coefficient] using HomogeneousLinearForm.eq_sum (pderiv i P) hh

theorem polynomial_identity (P : MvPolynomial σ R) (hP : P.IsHomogeneous 2) :
    (∑ i, ∑ j, C (entry P i j) * X i * X j) = 2 • P := by
  calc
    _ = ∑ i, X i * pderiv i P := by
      apply sum_congr rfl
      intro i _
      rw [gradient P hP i, mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := hP.sum_X_mul_pderiv

theorem evaluation_identity (P : MvPolynomial σ R) (hP : P.IsHomogeneous 2) (v : σ → R) :
    (∑ i, ∑ j, entry P i j * v i * v j) = 2 * eval v P := by
  have he := congrArg (eval v) (polynomial_identity P hP)
  simpa only [map_sum, map_mul, eval_C, eval_X, nsmul_eq_mul, map_natCast,
    Nat.cast_ofNat, eval_ofNat] using he

end PaperP1.HomogeneousQuadraticHessian
