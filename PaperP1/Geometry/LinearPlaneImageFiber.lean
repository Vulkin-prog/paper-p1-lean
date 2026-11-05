module

public import PaperP1.Geometry.LinearPlaneMinimalEquation
public import PaperP1.Algebra.PrimitiveDerivativeConductor
public import PaperP1.Algebra.ConductorFiberInjectivity
public import PaperP1.Algebra.PolynomialCoordinateDerivative
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Actual primitive-coordinate plane fibres are injective away from the homogeneous derivative -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPlaneImageFiber

open MvPolynomial LinearPlaneImage

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  [Algebra (MvPolynomial (Fin 2) F) A] [IsScalarTower F (MvPolynomial (Fin 2) F) A]

def denominator (y : A) : A :=
  Polynomial.aeval y (Polynomial.derivative (minpoly (MvPolynomial (Fin 2) F) y))

theorem adjoin_subset_range (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom) :
    (Algebra.adjoin (MvPolynomial (Fin 2) F) {y} : Set A) ⊆ (toSource (F := F) g y).range := by
  intro a ha
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, hp⟩ := ha
  change Polynomial.aeval y p = a at hp
  refine ⟨Ideal.Quotient.mk (ideal g y) ((finSuccEquiv F 2).symm p), ?_⟩
  change toSource (F := F) g y (Ideal.Quotient.mk (ideal g y) ((finSuccEquiv F 2).symm p)) = a
  rw [toSource_mk, LinearPlaneMinimalEquation.evaluation_factor g y hsource]
  change Polynomial.aeval y (finSuccEquiv F 2 ((finSuccEquiv F 2).symm p)) = a
  rw [AlgEquiv.apply_symm_apply]
  exact hp

theorem denominator_is_partial (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom) :
    denominator (F := F) y = aeval (R := F) (coordinates g y)
      (pderiv 0 (LinearPlaneMinimalEquation.equation (F := F) y)) := by
  rw [LinearPlaneMinimalEquation.evaluation_factor g y hsource]
  change Polynomial.aeval y (Polynomial.derivative (minpoly (MvPolynomial (Fin 2) F) y)) =
    Polynomial.aeval y (finSuccEquiv F 2 (pderiv 0 (LinearPlaneMinimalEquation.equation (F := F) y)))
  rw [PolynomialCoordinateDerivative.finSucc_pderiv_zero,
    LinearPlaneMinimalEquation.equation, AlgEquiv.apply_symm_apply]

theorem denominator_homogeneous (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (d : ℕ) (hq : (LinearPlaneMinimalEquation.equation (F := F) y).IsHomogeneous d) :
    denominator (F := F) y ∈ H (d - 1) := by
  rw [denominator_is_partial g y hsource]
  exact GradedPolynomialGenerators.eval_homogeneous H (coordinates g y) (coordinates_mem H g hg y hy)
    (d - 1) _ hq.pderiv

variable [IsDomain A]
  {K L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial (Fin 2) F) K] [Algebra K L] [Algebra A L] [Algebra (MvPolynomial (Fin 2) F) L]
  [IsScalarTower (MvPolynomial (Fin 2) F) K L] [IsScalarTower (MvPolynomial (Fin 2) F) A L]
  [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing A L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem conductor (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    ∀ a : A, denominator (F := F) y * a ∈ (toSource (F := F) g y).range := by
  have hfin : Module.Finite (MvPolynomial (Fin 2) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfin
  intro a
  apply adjoin_subset_range g y hsource
  exact PrimitiveDerivativeConductor.source_finite (K := K) (L := L) y hprimitive a

include K L in
omit [FiniteDimensional K L] [IsFractionRing A L] [IsScalarTower F (MvPolynomial (Fin 2) F) A] in
theorem denominator_ne_zero (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite) : denominator (F := F) y ≠ 0 := by
  have hfin : Module.Finite (MvPolynomial (Fin 2) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfin
  exact PrimitiveDerivativeConductor.source_derivative_ne_zero (K := K) (L := L) y (IsIntegral.of_finite _ y)

theorem evaluations_equal {Ω : Type*} [Field Ω] [Algebra F Ω]
    (g : Fin 2 → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤)
    (φ ψ : A →ₐ[F] Ω) (hagrees : ∀ b : CoordinateRing (F := F) g y, φ (toSource g y b) = ψ (toSource g y b))
    (hδ : φ (denominator (F := F) y) ≠ 0) : φ = ψ := by
  apply ConductorFiberInjectivity.evaluations_equal (toSource (F := F) g y).range (denominator (F := F) y)
    (conductor g y hsource hfinite hprimitive) φ ψ _ hδ
  intro a ha
  obtain ⟨b, rfl⟩ := ha
  exact hagrees b

end PaperP1.LinearPlaneImageFiber
