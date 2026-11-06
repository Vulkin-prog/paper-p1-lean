module

public import PaperP1.Geometry.LinearHypersurfaceImage
public import PaperP1.Algebra.PrimitiveBirationalFractionRing

/-! # The literal primitive-coordinate hypersurface image is birational and preserves the normalization rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHypersurfaceImageBirational

open MvPolynomial LinearHypersurfaceImage

variable {m : ℕ} {F A : Type*} [Field F] [CommRing A] [Algebra F A] (g : Fin m → A) (y : A)

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring

variable [Algebra (MvPolynomial (Fin m) F) A]

local instance imageParameterAlgebra : Algebra (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) :=
  (parameterMap (F := F) g y).toRingHom.toAlgebra

local instance imageSourceAlgebra : Algebra (CoordinateRing (F := F) g y) A :=
  (toSource (F := F) g y).toRingHom.toAlgebra

variable (K L : Type*) [Field K] [Field L]
  [Algebra (MvPolynomial (Fin m) F) K] [Algebra A L] [Algebra (MvPolynomial (Fin m) F) L] [Algebra K L]
  [IsScalarTower (MvPolynomial (Fin m) F) A L] [IsScalarTower (MvPolynomial (Fin m) F) K L]
  [IsFractionRing (MvPolynomial (Fin m) F) K] [IsFractionRing A L]

local instance imageFractionAlgebra : Algebra (CoordinateRing (F := F) g y) L :=
  ((algebraMap A L).comp (toSource (F := F) g y).toRingHom).toAlgebra

local instance imageFractionTower : IsScalarTower (CoordinateRing (F := F) g y) A L :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

omit [IsFractionRing A L] in
theorem baseFractionTower
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom) :
    IsScalarTower (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) L :=
  IsScalarTower.of_algebraMap_eq (fun P ↦ by
    change algebraMap (MvPolynomial (Fin m) F) L P = algebraMap A L (toSource g y (parameterMap g y P))
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin m) F) A L]
    rw [DFunLike.congr_fun hsource P]
    change algebraMap A L (aeval g P) = algebraMap A L (toSource g y (parameterMap g y P))
    exact congrArg (algebraMap A L) (DFunLike.congr_fun (parameterMap_toSource g y) P).symm)

theorem fraction_ring (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    IsFractionRing (CoordinateRing (F := F) g y) L := by
  let : IsScalarTower (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) L :=
    baseFractionTower g y L hsource
  have hbinj : Function.Injective (algebraMap (CoordinateRing (F := F) g y) L) :=
    (IsFractionRing.injective A L).comp (toSource_injective g y)
  apply PrimitiveBirationalFractionRing.fraction_ring (R := MvPolynomial (Fin m) F) (K := K)
    hbinj (algebraMap A L y) _ hprimitive
  refine ⟨Ideal.Quotient.mk (ideal g y) (X 0), ?_⟩
  change algebraMap A L (toSource g y (Ideal.Quotient.mk (ideal g y) (X 0))) = algebraMap A L y
  rw [primitive_coordinate]

theorem rank_one (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    Module.finrank (CoordinateRing (F := F) g y) A = 1 := by
  let : IsFractionRing (CoordinateRing (F := F) g y) L := fraction_ring g y K L hsource hprimitive
  have he := IsFractionRing.finrank_eq (CoordinateRing (F := F) g y) L A L
  simpa only [Module.finrank_self] using he.symm

theorem normalization_rank (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    Module.finrank (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) =
      Module.finrank (MvPolynomial (Fin m) F) A := by
  let : IsFractionRing (CoordinateRing (F := F) g y) L := fraction_ring g y K L hsource hprimitive
  let : IsScalarTower (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) L :=
    baseFractionTower g y L hsource
  exact (IsFractionRing.finrank_left_eq (MvPolynomial (Fin m) F) (CoordinateRing (F := F) g y) L).trans
    (IsFractionRing.finrank_left_eq (MvPolynomial (Fin m) F) A L).symm

end PaperP1.LinearHypersurfaceImageBirational
