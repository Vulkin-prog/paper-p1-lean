module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.Divisibility.Units

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonzeroScalarPolynomial

open MvPolynomial

variable {F σ : Type*} [Field F]

theorem constant_isUnit (c : F) (hc : c ≠ 0) : IsUnit (C c : MvPolynomial σ F) :=
  (isUnit_iff_ne_zero.mpr hc).map C

theorem dvd_scalar_right (c : F) (hc : c ≠ 0) (P Q : MvPolynomial σ F) :
    P ∣ C c * Q ↔ P ∣ Q := (constant_isUnit (σ := σ) c hc).dvd_mul_left

theorem scalar_dvd (c : F) (hc : c ≠ 0) (P Q : MvPolynomial σ F) :
    C c * P ∣ Q ↔ P ∣ Q := (constant_isUnit (σ := σ) c hc).mul_left_dvd

theorem irreducible_scalar (c : F) (hc : c ≠ 0) (P : MvPolynomial σ F) :
    Irreducible (C c * P) ↔ Irreducible P := irreducible_isUnit_mul (constant_isUnit (σ := σ) c hc)

end PaperP1.NonzeroScalarPolynomial
