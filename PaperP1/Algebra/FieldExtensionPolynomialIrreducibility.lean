module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Actual coefficient-field extension reflects polynomial units, irreducibility and hypersurface primeness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FieldExtensionPolynomialIrreducibility

open MvPolynomial

variable {F K σ : Type*} [Field F] [Field K]

theorem unit_of_map (f : F →+* K) (p : MvPolynomial σ F) (hp : IsUnit (map f p)) : IsUnit p := by
  have h := MvPolynomial.isUnit_iff.mp hp
  apply MvPolynomial.isUnit_iff.mpr
  constructor
  · have hc : IsUnit (f (p.coeff 0)) := by simpa only [coeff_map] using h.1
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hc.ne_zero (by rw [hz, map_zero])
  · intro m hm
    have hc : IsNilpotent (f (p.coeff m)) := by simpa only [coeff_map] using h.2 m hm
    exact (IsNilpotent.map_iff f.injective).mp hc

theorem irreducible_of_map (f : F →+* K) (p : MvPolynomial σ F)
    (hp : Irreducible (map f p)) : Irreducible p := by
  let : IsLocalHom (map (σ := σ) f) := ⟨fun p hp ↦ unit_of_map f p hp⟩
  exact hp.of_map

theorem prime_span_of_irreducible_map (f : F →+* K) (p : MvPolynomial σ F)
    (hp : Irreducible (map f p)) : (Ideal.span {p}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (irreducible_of_map f p hp).prime

end PaperP1.FieldExtensionPolynomialIrreducibility
