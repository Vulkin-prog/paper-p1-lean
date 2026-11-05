module

public import PaperP1.Algebra.HomogenizationIrreducibilityReflection

/-! # Irreducibility of a plane equation descends through a field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarIrreducibilityReflection

open Polynomial PaperP1.PolynomialScalarProjection

theorem unit_reflection {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hi : Function.Injective f) (hu : ∀ r, IsUnit (f r) → IsUnit r)
    (P : R[X]) (hP : IsUnit (P.map f)) : IsUnit P := by
  have hd : P.natDegree = 0 := by
    rw [← Polynomial.natDegree_map_eq_of_injective hi P]
    exact Polynomial.natDegree_eq_zero_of_isUnit hP
  have he := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [he, Polynomial.map_C] at hP
  have hc := hu (P.coeff 0) (Polynomial.isUnit_C.mp hP)
  rw [he]
  exact Polynomial.isUnit_C.mpr hc

theorem irreducible_of_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    (P : K[X][X]) (hP : Irreducible (extend P : L[X][X])) : Irreducible P := by
  let f : K →+* L := algebraMap K L
  let φ : K[X] →+* L[X] := Polynomial.mapRingHom f
  let ψ : K[X][X] →+* L[X][X] := Polynomial.mapRingHom φ
  have hi : Function.Injective f := (algebraMap K L).injective
  have hiφ : Function.Injective φ := Polynomial.map_injective f hi
  have hbase (a : K) (ha : IsUnit (f a)) : IsUnit a := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply ha.ne_zero
    rw [hz, map_zero]
  have hinner (A : K[X]) (hA : IsUnit (φ A)) : IsUnit A :=
    unit_reflection f hi hbase A hA
  have hunit (A : K[X][X]) (hA : IsUnit (ψ A)) : IsUnit A :=
    unit_reflection φ hiφ hinner A hA
  change Irreducible (ψ P) at hP
  refine ⟨fun hu ↦ hP.1 (hu.map ψ), ?_⟩
  intro A B hAB
  have he : ψ P = ψ A * ψ B := by rw [hAB, map_mul]
  exact (hP.2 he).imp (hunit A) (hunit B)

theorem geometric_rational_irreducible (G : ℤ[X][X]) (hne : G ≠ 0)
    (hG : PaperP1.GeometricFactorSwap.Geometric G) :
    Irreducible (PaperP1.RationalBivariateIrreducibility.rationalize G) := by
  apply irreducible_of_extension (L := ℂ)
  rw [PaperP1.ComplexProjectiveIrreducibility.rational_extension]
  exact (PaperP1.HomogenizationIrreducibilityReflection.geometric_iff_affine G hne).mp hG

end PaperP1.ScalarIrreducibilityReflection
