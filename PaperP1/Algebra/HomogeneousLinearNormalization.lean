module

public import PaperP1.Algebra.HomogeneousLinearShear
public import PaperP1.Algebra.PolynomialCoordinateProjectionFinite
public import PaperP1.Algebra.HomogeneousQuotientGrading

/-! # Actual finite linear normalization for homogeneous hypersurface quotients

A nonzero homogeneous relation over an infinite field gives a finite map
from a polynomial algebra with one fewer variable. The parameters are
proved to lie in the actual degree-one quotient pieces.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousLinearNormalization

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring
attribute [local instance] MvPolynomial.gradedAlgebra

variable (I : Ideal (MvPolynomial (Fin (n + 1)) F)) (v : Fin n → F)

local instance quotientRing : CommRing (MvPolynomial (Fin (n + 1)) F ⧸ I) := inferInstance
local instance quotientSemiring : Semiring (MvPolynomial (Fin (n + 1)) F ⧸ I) :=
  (quotientRing I).toSemiring

def transformedIdeal : Ideal (MvPolynomial (Fin (n + 1)) F) :=
  I.map (HomogeneousLinearShear.equiv v).toRingHom

def quotientEquiv : (MvPolynomial (Fin (n + 1)) F ⧸ I) ≃ₐ[F]
    (MvPolynomial (Fin (n + 1)) F ⧸ transformedIdeal I v) :=
  Ideal.quotientEquivAlg I (transformedIdeal I v) (HomogeneousLinearShear.equiv v) rfl

theorem quotientEquiv_mk (p : MvPolynomial (Fin (n + 1)) F) :
    quotientEquiv I v (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (transformedIdeal I v) (HomogeneousLinearShear.substitute v p) := rfl

def parameterMap : MvPolynomial (Fin n) F →ₐ[F] (MvPolynomial (Fin (n + 1)) F ⧸ I) :=
  (quotientEquiv I v).symm.toAlgHom.comp
    (PolynomialCoordinateProjectionFinite.parameterMap (transformedIdeal I v))

theorem parameterMap_X (i : Fin n) : parameterMap I v (X i) =
    Ideal.Quotient.mk I (HomogeneousLinearShear.substitute (-v) (X i.succ)) := by
  apply (quotientEquiv I v).injective
  change quotientEquiv I v ((quotientEquiv I v).symm
    (PolynomialCoordinateProjectionFinite.parameterMap (transformedIdeal I v) (X i))) = _
  rw [AlgEquiv.apply_symm_apply, PolynomialCoordinateProjectionFinite.parameterMap_X, quotientEquiv_mk]
  have he := (HomogeneousLinearShear.equiv v).apply_symm_apply (X i.succ)
  exact congrArg (Ideal.Quotient.mk (transformedIdeal I v)) he.symm

theorem parameter_mem (i : Fin n) : parameterMap I v (X i) ∈
    HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) F) I 1 := by
  rw [parameterMap_X]
  exact Submodule.mem_map.mpr ⟨_, HomogeneousLinearShear.homogeneous (-v) _
    (isHomogeneous_X F i.succ), rfl⟩

theorem parameterMap_eq_aeval : parameterMap I v = aeval (fun i ↦ parameterMap I v (X i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact (aeval_X (fun i ↦ parameterMap I v (X i)) i).symm

theorem finite (p : MvPolynomial (Fin (n + 1)) F) (hp : p ∈ I)
    (hlc : IsUnit (finSuccEquiv F n (HomogeneousLinearShear.substitute v p)).leadingCoeff) :
    (parameterMap I v).Finite := by
  have hm : HomogeneousLinearShear.substitute v p ∈ transformedIdeal I v :=
    Ideal.mem_map_of_mem (HomogeneousLinearShear.equiv v).toRingHom hp
  exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective (quotientEquiv I v).symm.toAlgHom
    (quotientEquiv I v).symm.surjective)
    (PolynomialCoordinateProjectionFinite.finite (transformedIdeal I v) _ hm hlc)

/-- The finiteness and degree-one statements concern the same literal parameter evaluation. -/
theorem exists_parameters [Infinite F] {e : ℕ} (p : MvPolynomial (Fin (n + 1)) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) (hmem : p ∈ I) :
    ∃ g : Fin n → (MvPolynomial (Fin (n + 1)) F ⧸ I),
      (∀ i, g i ∈ HomogeneousQuotientGrading.piece
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) F) I 1) ∧ (aeval (R := F) g).Finite := by
  obtain ⟨v, hv⟩ := HomogeneousLinearShear.exists_unit_leadingCoeff p hp hp0
  refine ⟨fun i ↦ parameterMap I v (X i), parameter_mem I v, ?_⟩
  rw [← parameterMap_eq_aeval]
  exact finite I v p hmem hv

end PaperP1.HomogeneousLinearNormalization
