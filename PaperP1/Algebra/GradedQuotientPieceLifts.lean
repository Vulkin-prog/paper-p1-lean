module

public import PaperP1.Algebra.GradedQuotientHilbertMonotonicity
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

/-! # Actual homogeneous quotient pieces have linear lifts into the original homogeneous pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientPieceLifts

open GradedQuotientHilbertMonotonicity

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) (I : Ideal A) (n : ℕ)

theorem exists_lift : ∃ s : HomogeneousQuotientGrading.piece H I n →ₗ[F] H n,
    (quotientMap H I n).comp s = LinearMap.id :=
  (quotientMap H I n).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (quotientMap_surjective H I n))

def lift : HomogeneousQuotientGrading.piece H I n →ₗ[F] H n := (exists_lift H I n).choose

theorem quotient_lift (x : HomogeneousQuotientGrading.piece H I n) :
    quotientMap H I n (lift H I n x) = x :=
  LinearMap.congr_fun (exists_lift H I n).choose_spec x

theorem lift_quotient_value (x : HomogeneousQuotientGrading.piece H I n) :
    Ideal.Quotient.mk I (lift H I n x : A) = (x : A ⧸ I) :=
  congrArg Subtype.val (quotient_lift H I n x)

end PaperP1.GradedQuotientPieceLifts
