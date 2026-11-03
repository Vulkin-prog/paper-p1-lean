module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # An actual homogeneous polynomial in one variable is a scalar monomial -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.UnivariateHomogeneousPolynomial

variable {F σ : Type*} [CommSemiring F] [Unique σ]

theorem exponent_eq_single (d : σ →₀ ℕ) : d = Finsupp.single default d.degree := by
  have hd : d.degree = d default := by
    simpa only [Finsupp.degree_single] using congrArg (fun a : σ →₀ ℕ ↦ a.degree) (Finsupp.unique_single d)
  exact (Finsupp.unique_single d).trans (congrArg (Finsupp.single default) hd.symm)

theorem homogeneous_eq {n : ℕ} (p : MvPolynomial σ F) (hp : p.IsHomogeneous n) :
    p = MvPolynomial.C (p.coeff (Finsupp.single default n)) * MvPolynomial.X default ^ n := by
  classical
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  ext d
  by_cases hd : d.degree = n
  · have he : d = Finsupp.single default n := (exponent_eq_single d).trans (congrArg (Finsupp.single default) hd)
    rw [he]
    simp
  · rw [hp.coeff_eq_zero hd]
    have hne : Finsupp.single default n ≠ d := by
      intro he
      apply hd
      rw [← he, Finsupp.degree_single]
    simp [MvPolynomial.coeff_monomial, hne]

theorem factor_variable {n : ℕ} (hn : 0 < n) (p : MvPolynomial σ F) (hp : p.IsHomogeneous n) :
    ∃ q : MvPolynomial σ F, q.IsHomogeneous (n - 1) ∧ q * MvPolynomial.X default = p := by
  let a := p.coeff (Finsupp.single default n)
  refine ⟨MvPolynomial.C a * MvPolynomial.X default ^ (n - 1),
    MvPolynomial.isHomogeneous_C_mul_X_pow a default (n - 1), ?_⟩
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  exact (homogeneous_eq p hp).symm

end PaperP1.UnivariateHomogeneousPolynomial
