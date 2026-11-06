module

public import PaperP1.Geometry.LinearHypersurfaceMinimalEquation
public import PaperP1.Algebra.PrimitiveDerivativeConductor
public import PaperP1.Algebra.ConductorFiberInjectivity
public import PaperP1.Algebra.PolynomialCoordinateDerivative
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Actual primitive-coordinate hypersurface fibres are injective away from the homogeneous derivative -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHypersurfaceImageFiber

open MvPolynomial LinearHypersurfaceImage

variable {m : ℕ} {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  [Algebra (MvPolynomial (Fin m) F) A] [IsScalarTower F (MvPolynomial (Fin m) F) A]

def denominator (y : A) : A :=
  Polynomial.aeval y (Polynomial.derivative (minpoly (MvPolynomial (Fin m) F) y))

theorem adjoin_subset_range (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom) :
    (Algebra.adjoin (MvPolynomial (Fin m) F) {y} : Set A) ⊆ (toSource (F := F) g y).range := by
  intro a ha
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, hp⟩ := ha
  change Polynomial.aeval y p = a at hp
  refine ⟨Ideal.Quotient.mk (ideal g y) ((finSuccEquiv F m).symm p), ?_⟩
  change toSource (F := F) g y (Ideal.Quotient.mk (ideal g y) ((finSuccEquiv F m).symm p)) = a
  rw [toSource_mk, LinearHypersurfaceMinimalEquation.evaluation_factor g y hsource]
  change Polynomial.aeval y (finSuccEquiv F m ((finSuccEquiv F m).symm p)) = a
  rw [AlgEquiv.apply_symm_apply]
  exact hp

theorem denominator_is_partial (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom) :
    denominator (m := m) (F := F) y = aeval (R := F) (coordinates g y)
      (pderiv 0 (LinearHypersurfaceMinimalEquation.equation (m := m) (F := F) y)) := by
  rw [LinearHypersurfaceMinimalEquation.evaluation_factor g y hsource]
  change Polynomial.aeval y (Polynomial.derivative (minpoly (MvPolynomial (Fin m) F) y)) =
    Polynomial.aeval y (finSuccEquiv F m (pderiv 0 (LinearHypersurfaceMinimalEquation.equation (m := m) (F := F) y)))
  rw [PolynomialCoordinateDerivative.finSucc_pderiv_zero,
    LinearHypersurfaceMinimalEquation.equation, AlgEquiv.apply_symm_apply]

theorem denominator_homogeneous (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (d : ℕ) (hq : (LinearHypersurfaceMinimalEquation.equation (m := m) (F := F) y).IsHomogeneous d) :
    denominator (m := m) (F := F) y ∈ H (d - 1) := by
  rw [denominator_is_partial g y hsource]
  exact GradedPolynomialGenerators.eval_homogeneous H (coordinates g y) (coordinates_mem H g hg y hy)
    (d - 1) _ hq.pderiv

variable [IsDomain A]
  {K L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial (Fin m) F) K] [Algebra K L] [Algebra A L] [Algebra (MvPolynomial (Fin m) F) L]
  [IsScalarTower (MvPolynomial (Fin m) F) K L] [IsScalarTower (MvPolynomial (Fin m) F) A L]
  [IsFractionRing (MvPolynomial (Fin m) F) K] [IsFractionRing A L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem conductor (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    ∀ a : A, denominator (m := m) (F := F) y * a ∈ (toSource (F := F) g y).range := by
  have hfin : Module.Finite (MvPolynomial (Fin m) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin m) F) A := hfin
  intro a
  apply adjoin_subset_range g y hsource
  exact PrimitiveDerivativeConductor.source_finite (K := K) (L := L) y hprimitive a

include K L in
omit [FiniteDimensional K L] [IsFractionRing A L] [IsScalarTower F (MvPolynomial (Fin m) F) A] in
theorem denominator_ne_zero (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite) : denominator (m := m) (F := F) y ≠ 0 := by
  have hfin : Module.Finite (MvPolynomial (Fin m) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin m) F) A := hfin
  exact PrimitiveDerivativeConductor.source_derivative_ne_zero (K := K) (L := L) y (IsIntegral.of_finite _ y)

theorem evaluations_equal {Ω : Type*} [Field Ω] [Algebra F Ω]
    (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤)
    (φ ψ : A →ₐ[F] Ω) (hagrees : ∀ b : CoordinateRing (F := F) g y, φ (toSource g y b) = ψ (toSource g y b))
    (hδ : φ (denominator (m := m) (F := F) y) ≠ 0) : φ = ψ := by
  apply ConductorFiberInjectivity.evaluations_equal (toSource (F := F) g y).range (denominator (m := m) (F := F) y)
    (conductor g y hsource hfinite hprimitive) φ ψ _ hδ
  intro a ha
  obtain ⟨b, rfl⟩ := ha
  exact hagrees b

end PaperP1.LinearHypersurfaceImageFiber
