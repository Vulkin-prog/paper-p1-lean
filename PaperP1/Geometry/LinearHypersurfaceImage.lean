module

public import PaperP1.Algebra.GradedPolynomialPresentation
public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.FiniteInjectiveIntermediate
public import Mathlib.RingTheory.Polynomial.Basic

/-! # The actual homogeneous hypersurface image of any finite family of linear parameters and one linear coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHypersurfaceImage

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {F A : Type*} [Field F] [CommRing A] [Algebra F A]

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring

def coordinates (g : Fin m → A) (y : A) : Fin (m + 1) → A := Fin.cons y g

def ideal (g : Fin m → A) (y : A) : Ideal (MvPolynomial (Fin (m + 1)) F) :=
  RingHom.ker (aeval (coordinates g y))

abbrev CoordinateRing (g : Fin m → A) (y : A) := MvPolynomial (Fin (m + 1)) F ⧸ ideal g y

def toSource (g : Fin m → A) (y : A) : CoordinateRing (F := F) g y →ₐ[F] A :=
  let hkill : ∀ P, P ∈ ideal (F := F) g y → aeval (coordinates g y) P = 0 := fun _ hP ↦ hP
  Ideal.Quotient.liftₐ (ideal g y) (aeval (coordinates g y)) hkill

def piece (g : Fin m → A) (y : A) (n : ℕ) : Submodule F (CoordinateRing (F := F) g y) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin (m + 1)) F) (ideal g y) n

theorem coordinates_mem (H : ℕ → Submodule F A) (g : Fin m → A) (hg : ∀ i, g i ∈ H 1)
    (y : A) (hy : y ∈ H 1) : ∀ i, coordinates g y i ∈ H 1 := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hy
  · exact hg j

theorem ideal_homogeneous (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1) :
    (ideal (F := F) g y).IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) F) :=
  GradedPolynomialPresentation.kernel_homogeneous H (coordinates g y) (coordinates_mem H g hg y hy)

theorem ideal_prime [IsDomain A] (g : Fin m → A) (y : A) : (ideal (F := F) g y).IsPrime :=
  RingHom.ker_isPrime (aeval (R := F) (coordinates g y))

@[instance_reducible]
def grading (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1) :
    GradedAlgebra (piece (F := F) g y) :=
  HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin (m + 1)) F) (ideal g y)
    (ideal_homogeneous H g hg y hy)

theorem toSource_mk (g : Fin m → A) (y : A) (P : MvPolynomial (Fin (m + 1)) F) :
    toSource g y (Ideal.Quotient.mk (ideal g y) P) = aeval (coordinates g y) P := rfl

theorem toSource_injective (g : Fin m → A) (y : A) : Function.Injective (toSource (F := F) g y) := by
  change Function.Injective (RingHom.kerLift (aeval (R := F) (coordinates g y)).toRingHom)
  exact RingHom.kerLift_injective _

theorem piece_finite (g : Fin m → A) (y : A) (n : ℕ) : Module.Finite F (piece (F := F) g y n) := by
  let : Module.Finite F (homogeneousSubmodule (Fin (m + 1)) F n) := MvPolynomialHilbert.piece_finite F (Fin (m + 1)) n
  exact HomogeneousQuotientGrading.piece_finite _ (ideal g y) n

theorem toSource_mem (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (n : ℕ) (a : CoordinateRing (F := F) g y) (ha : a ∈ piece (F := F) g y n) :
    toSource g y a ∈ H n := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp ha
  change toSource g y (Ideal.Quotient.mk (ideal g y) P) ∈ H n
  rw [toSource_mk]
  exact GradedPolynomialGenerators.eval_homogeneous H (coordinates g y) (coordinates_mem H g hg y hy) n P hP

def parameterMap (g : Fin m → A) (y : A) : MvPolynomial (Fin m) F →ₐ[F] CoordinateRing (F := F) g y :=
  aeval (fun i ↦ Ideal.Quotient.mk (ideal g y) (X i.succ))

theorem parameterMap_X (g : Fin m → A) (y : A) (i : Fin m) :
    parameterMap (F := F) g y (X i) = Ideal.Quotient.mk (ideal g y) (X i.succ) := aeval_X _ i

theorem parameter_mem (g : Fin m → A) (y : A) (i : Fin m) :
    parameterMap (F := F) g y (X i) ∈ piece (F := F) g y 1 := by
  rw [parameterMap_X]
  exact Submodule.mem_map.mpr ⟨X i.succ, isHomogeneous_X F i.succ, rfl⟩

theorem parameterMap_toSource (g : Fin m → A) (y : A) :
    (toSource (F := F) g y).comp (parameterMap g y) = aeval (R := F) g := by
  apply MvPolynomial.algHom_ext
  intro i
  change toSource g y (parameterMap g y (X i)) = aeval g (X i)
  rw [parameterMap_X, toSource_mk]
  simp only [aeval_X, coordinates, Fin.cons_succ]

theorem parameterMap_finite (g : Fin m → A) (y : A) (hfinite : (aeval (R := F) g).Finite) :
    (parameterMap (F := F) g y).Finite := by
  apply FiniteInjectiveIntermediate.finite_factor _ (toSource g y) (toSource_injective g y)
  rw [parameterMap_toSource]
  exact hfinite

theorem toSource_finite (g : Fin m → A) (y : A) (hfinite : (aeval (R := F) g).Finite) :
    (toSource (F := F) g y).Finite := by
  apply AlgHom.Finite.of_comp_finite (f := parameterMap g y)
  rw [parameterMap_toSource]
  exact hfinite

theorem parameterMap_injective (g : Fin m → A) (y : A) (hinj : Function.Injective (aeval (R := F) g)) :
    Function.Injective (parameterMap (F := F) g y) := by
  intro P Q he
  apply hinj
  have hh := congrArg (toSource (F := F) g y) he
  change ((toSource g y).comp (parameterMap g y)) P = ((toSource g y).comp (parameterMap g y)) Q at hh
  rwa [parameterMap_toSource] at hh

theorem primitive_coordinate (g : Fin m → A) (y : A) :
    toSource (F := F) g y (Ideal.Quotient.mk (ideal g y) (X 0)) = y := by
  rw [toSource_mk]
  simp only [aeval_X, coordinates, Fin.cons_zero]

end PaperP1.LinearHypersurfaceImage
