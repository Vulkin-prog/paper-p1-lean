module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Polynomial.Tower

/-! # The actual primitive minimal-polynomial derivative clears every integral coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveDerivativeConductor

open Polynomial

variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsFractionRing R K] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem integral_mul_derivative (x y : L) (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hprimitive : Algebra.adjoin K {x} = ⊤) :
    aeval x (derivative (minpoly K x)) * y ∈ Algebra.adjoin R {x} := by
  have hS : Algebra.adjoin R {x} ≤ integralClosure R L := Algebra.adjoin_le (by
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hx)
  have hdual : y ∈ (Algebra.traceForm K L).dualSubmodule (Algebra.adjoin R {x}).toSubmodule := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    have hzint : IsIntegral R z := hS hz
    rw [Algebra.traceForm_apply, Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := K) (F := L) (hy.mul hzint))
  rw [traceForm_dualSubmodule_adjoin R K hprimitive hx] at hdual
  have hd : aeval x (derivative (minpoly K x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero (minpoly.aeval K x)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hd)] at hdual
  rw [← Subalgebra.mem_toSubmodule]
  simpa only [inv_inv] using hdual

theorem integral_mul_ring_derivative (x y : L) (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hprimitive : Algebra.adjoin K {x} = ⊤) :
    aeval x (derivative (minpoly R x)) * y ∈ Algebra.adjoin R {x} := by
  have hh := integral_mul_derivative (K := K) x y hx hy hprimitive
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, derivative_map, aeval_map_algebraMap] at hh
  exact hh

variable {A : Type*} [CommRing A] [IsDomain A] [Algebra R A] [Algebra A L]
  [IsScalarTower R A L] [IsFractionRing A L]

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsFractionRing A L] in
theorem source_derivative_image (x : A) (hx : IsIntegral R x) :
    aeval (algebraMap A L x) (derivative (minpoly K (algebraMap A L x))) =
      algebraMap A L (aeval x (derivative (minpoly R x))) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hx, derivative_map,
    aeval_map_algebraMap, aeval_algebraMap_apply]

theorem source_integral (x a : A) (hx : IsIntegral R x) (ha : IsIntegral R a)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L x} = ⊤) :
    aeval x (derivative (minpoly R x)) * a ∈ Algebra.adjoin R {x} := by
  have hprim : Algebra.adjoin K {algebraMap A L x} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hprimitive]
    rfl
  have hxL : IsIntegral R (algebraMap A L x) := hx.map (IsScalarTower.toAlgHom R A L)
  have haL : IsIntegral R (algebraMap A L a) := ha.map (IsScalarTower.toAlgHom R A L)
  have hh := integral_mul_derivative (K := K) (algebraMap A L x) (algebraMap A L a) hxL haL hprim
  rw [source_derivative_image (K := K) x hx, ← map_mul] at hh
  let f := IsScalarTower.toAlgHom R A L
  have hmem : f (aeval x (derivative (minpoly R x)) * a) ∈ (Algebra.adjoin R {x}).map f := by
    rw [AlgHom.map_adjoin_singleton]
    exact hh
  obtain ⟨b, hb, he⟩ := Subalgebra.mem_map.mp hmem
  have hbe : b = aeval x (derivative (minpoly R x)) * a := IsFractionRing.injective A L he
  exact hbe ▸ hb

theorem source_finite [Module.Finite R A] (x : A)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L x} = ⊤) :
    ∀ a : A, aeval x (derivative (minpoly R x)) * a ∈ Algebra.adjoin R {x} := by
  intro a
  exact source_integral (K := K) (L := L) x a (IsIntegral.of_finite R x) (IsIntegral.of_finite R a) hprimitive

include K L in
omit [FiniteDimensional K L] [IsFractionRing A L] in
theorem source_derivative_ne_zero (x : A) (hx : IsIntegral R x) :
    aeval x (derivative (minpoly R x)) ≠ 0 := by
  have hd : aeval (algebraMap A L x) (derivative (minpoly K (algebraMap A L x))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K (algebraMap A L x)).aeval_derivative_ne_zero
      (minpoly.aeval K (algebraMap A L x))
  intro hz
  apply hd
  rw [source_derivative_image (K := K) x hx, hz, map_zero]

end PaperP1.PrimitiveDerivativeConductor
