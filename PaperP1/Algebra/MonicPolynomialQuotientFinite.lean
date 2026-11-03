module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Basic

/-! # A polynomial quotient containing a monic relation is finite over its coefficient ring -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonicPolynomialQuotientFinite

variable {R : Type*} [CommRing R]

theorem of_monic_mem (I : Ideal (Polynomial R)) (p : Polynomial R)
    (hp : p.Monic) (hmem : p ∈ I) : Module.Finite R (Polynomial R ⧸ I) := by
  have := hp.finite_quotient
  have hle : Ideal.span {p} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hmem
  exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap
    (Ideal.Quotient.factor_surjective hle)

theorem of_unit_leadingCoeff_mem (I : Ideal (Polynomial R)) (p : Polynomial R)
    (hp : IsUnit p.leadingCoeff) (hmem : p ∈ I) : Module.Finite R (Polynomial R ⧸ I) := by
  exact of_monic_mem I (hp.unit⁻¹.val • p) (Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp)
    (Submodule.smul_of_tower_mem I hp.unit⁻¹.val hmem)

end PaperP1.MonicPolynomialQuotientFinite
