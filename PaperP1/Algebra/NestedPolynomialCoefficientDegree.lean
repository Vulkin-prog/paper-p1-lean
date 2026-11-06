module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Literal coefficient interchange and coefficient degree bounds for nested multivariate polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NestedPolynomialCoefficientDegree

open MvPolynomial
open scoped Classical

variable {R σ τ : Type*} [CommSemiring R]

theorem comm_monomial (m : σ →₀ ℕ) (n : τ →₀ ℕ) (c : R) :
    commAlgEquiv R σ τ (monomial m (monomial n c)) = monomial n (monomial m c) :=
  AddMonoidAlgebra.commAlgEquiv_single_single m n c

theorem coefficient_comm (P : MvPolynomial σ (MvPolynomial τ R)) (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    ((commAlgEquiv R σ τ P).coeff n).coeff m = (P.coeff m).coeff n := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | monomial a P =>
    induction P using MvPolynomial.induction_on' with
    | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
    | monomial b c =>
      rw [comm_monomial]
      by_cases ha : a = m <;> by_cases hb : b = n <;> simp [coeff_monomial, ha, hb]

theorem coefficient_degree_le (P : MvPolynomial σ (MvPolynomial τ R)) (m : σ →₀ ℕ) :
    (P.coeff m).totalDegree ≤ (commAlgEquiv R σ τ P).totalDegree := by
  rw [totalDegree]
  apply Finset.sup_le
  intro n hn
  apply le_totalDegree
  apply mem_support_iff.mpr
  intro hh
  have hc := mem_support_iff.mp hn
  apply hc
  rw [← coefficient_comm P m n, hh]
  simp

end PaperP1.NestedPolynomialCoefficientDegree
