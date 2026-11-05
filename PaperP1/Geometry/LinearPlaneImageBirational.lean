module

public import PaperP1.Geometry.LinearPlaneImage
public import PaperP1.Algebra.PrimitiveBirationalFractionRing
public import PaperP1.Algebra.FiniteParameterImageHilbert

/-! # The literal primitive-coordinate plane image is birational and has the original Hilbert degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPlaneImageBirational

open MvPolynomial LinearPlaneImage

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] (g : Fin 2 → A) (y : A)

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring

variable [Algebra (MvPolynomial (Fin 2) F) A]

local instance imageParameterAlgebra : Algebra (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) :=
  (parameterMap (F := F) g y).toRingHom.toAlgebra

local instance imageSourceAlgebra : Algebra (CoordinateRing (F := F) g y) A :=
  (toSource (F := F) g y).toRingHom.toAlgebra

variable (K L : Type*) [Field K] [Field L]
  [Algebra (MvPolynomial (Fin 2) F) K] [Algebra A L] [Algebra (MvPolynomial (Fin 2) F) L] [Algebra K L]
  [IsScalarTower (MvPolynomial (Fin 2) F) A L] [IsScalarTower (MvPolynomial (Fin 2) F) K L]
  [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing A L]

local instance imageFractionAlgebra : Algebra (CoordinateRing (F := F) g y) L :=
  ((algebraMap A L).comp (toSource (F := F) g y).toRingHom).toAlgebra

local instance imageFractionTower : IsScalarTower (CoordinateRing (F := F) g y) A L :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

omit [IsFractionRing A L] in
theorem baseFractionTower
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom) :
    IsScalarTower (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) L :=
  IsScalarTower.of_algebraMap_eq (fun P ↦ by
    change algebraMap (MvPolynomial (Fin 2) F) L P = algebraMap A L (toSource g y (parameterMap g y P))
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) F) A L]
    rw [DFunLike.congr_fun hsource P]
    change algebraMap A L (aeval g P) = algebraMap A L (toSource g y (parameterMap g y P))
    exact congrArg (algebraMap A L) (DFunLike.congr_fun (parameterMap_toSource g y) P).symm)

theorem fraction_ring (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    IsFractionRing (CoordinateRing (F := F) g y) L := by
  let : IsScalarTower (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) L :=
    baseFractionTower g y L hsource
  have hbinj : Function.Injective (algebraMap (CoordinateRing (F := F) g y) L) :=
    (IsFractionRing.injective A L).comp (toSource_injective g y)
  apply PrimitiveBirationalFractionRing.fraction_ring (R := MvPolynomial (Fin 2) F) (K := K)
    hbinj (algebraMap A L y) _ hprimitive
  refine ⟨Ideal.Quotient.mk (ideal g y) (X 0), ?_⟩
  change algebraMap A L (toSource g y (Ideal.Quotient.mk (ideal g y) (X 0))) = algebraMap A L y
  rw [primitive_coordinate]

theorem rank_one (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    Module.finrank (CoordinateRing (F := F) g y) A = 1 := by
  let : IsFractionRing (CoordinateRing (F := F) g y) L := fraction_ring g y K L hsource hprimitive
  have he := IsFractionRing.finrank_eq (CoordinateRing (F := F) g y) L A L
  simpa only [Module.finrank_self] using he.symm

theorem normalization_rank (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    Module.finrank (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) =
      Module.finrank (MvPolynomial (Fin 2) F) A := by
  let : IsFractionRing (CoordinateRing (F := F) g y) L := fraction_ring g y K L hsource hprimitive
  let : IsScalarTower (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) L :=
    baseFractionTower g y L hsource
  exact (IsFractionRing.finrank_left_eq (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) L).trans
    (IsFractionRing.finrank_left_eq (MvPolynomial (Fin 2) F) A L).symm

theorem exists_linear_hilbert (H : ℕ → Submodule F A) [GradedAlgebra H]
    (hg : ∀ i, g i ∈ H 1) (hy : y ∈ H 1)
    (hfinite : (aeval (R := F) g).Finite) (hinj : Function.Injective (aeval (R := F) g))
    (d : ℕ) (hrank : Module.finrank (MvPolynomial (Fin 2) F) A = d)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    ∃ b : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial (piece (F := F) g y)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b) := by
  let : GradedAlgebra (piece (F := F) g y) := grading H g hg y hy
  let : ∀ n, Module.Finite F (piece (F := F) g y n) := piece_finite g y
  let : IsFractionRing (CoordinateRing (F := F) g y) L := fraction_ring g y K L hsource hprimitive
  let : IsDomain (CoordinateRing (F := F) g y) := IsDomain.of_faithfulSMul (CoordinateRing (F := F) g y) L
  let gB : Fin 2 → CoordinateRing (F := F) g y := fun i ↦ Ideal.Quotient.mk (ideal g y) (X i.succ)
  have hgB (i : Fin 2) : gB i ∈ piece (F := F) g y 1 :=
    Submodule.mem_map.mpr ⟨X i.succ, isHomogeneous_X F i.succ, rfl⟩
  have hrankB : Module.finrank (MvPolynomial (Fin 2) F) (CoordinateRing (F := F) g y) = d :=
    (normalization_rank g y K L hsource hprimitive).trans hrank
  exact FiniteParameterImageHilbert.exists_linear_hilbert (piece (F := F) g y) gB hgB
    (parameterMap_finite g y hfinite) (parameterMap_injective g y hinj) d hrankB

end PaperP1.LinearPlaneImageBirational
