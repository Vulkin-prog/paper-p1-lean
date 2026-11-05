module

public import PaperP1.Arithmetic.IntegerLinearPlaneProjection
public import PaperP1.Geometry.PlaneImagePointSeparation

/-! # The actual bounded integer plane coordinates separate the original good source points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurveProjectionCoordinates

open MvPolynomial IntegerLinearPlaneProjection

variable {F : Type*} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))

def parameters (z : Fin n) (u : Fin n → ℕ) : Fin 2 → (MvPolynomial (Fin n) F ⧸ I) :=
  ![Ideal.Quotient.mk I (X z),
    Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))]

def primitive (v : Fin n → ℕ) : MvPolynomial (Fin n) F ⧸ I :=
  Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (v i : F)))

theorem evaluation_coordinates (z : Fin n) (u v : Fin n → ℕ) (w : Fin n → ℤ)
    (hw : ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0) (hz : w z = 1) :
    ∀ i, QuotientPointEvaluation.evaluation I (fun j ↦ (w j : F)) hw
      (LinearPlaneImage.coordinates (parameters I z u) (primitive I v) i) =
      (![ (coordinate v w : F), 1, (coordinate u w : F)] : Fin 3 → F) i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact quotient_evaluation I v w hw
  · fin_cases j
    · change QuotientPointEvaluation.evaluation I (fun j ↦ (w j : F)) hw
        (Ideal.Quotient.mk I (X z)) = 1
      rw [QuotientPointEvaluation.evaluation_X, hz, Int.cast_one]
    · exact quotient_evaluation I u w hw

variable [CharZero F] [I.IsPrime]
  [Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
  [IsScalarTower F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
  {K L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial (Fin 2) F) K] [Algebra K L]
  [Algebra (MvPolynomial (Fin n) F ⧸ I) L] [Algebra (MvPolynomial (Fin 2) F) L]
  [IsScalarTower (MvPolynomial (Fin 2) F) K L]
  [IsScalarTower (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) L]
  [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing (MvPolynomial (Fin n) F ⧸ I) L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem points_equal (z : Fin n) (u v : Fin n → ℕ)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) =
      (aeval (R := F) (parameters I z u)).toRingHom)
    (hfinite : (aeval (R := F) (parameters I z u)).Finite)
    (hprimitive : IntermediateField.adjoin K
      {algebraMap (MvPolynomial (Fin n) F ⧸ I) L (primitive I v)} = ⊤)
    (w t : Fin n → ℤ)
    (hw : ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (ht : ∀ P ∈ I, eval (fun i ↦ (t i : F)) P = 0)
    (hwz : w z = 1) (htz : t z = 1)
    (he : projection u v w = projection u v t)
    (hδ : QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) hw
      (LinearPlaneImageFiber.denominator (F := F) (primitive I v)) ≠ 0) : w = t := by
  have hx : coordinate u w = coordinate u t := congrArg Prod.fst he
  have hy : coordinate v w = coordinate v t := congrArg Prod.snd he
  have hcoords : ∀ i, QuotientPointEvaluation.evaluation I (fun j ↦ (w j : F)) hw
      (LinearPlaneImage.coordinates (parameters I z u) (primitive I v) i) =
      QuotientPointEvaluation.evaluation I (fun j ↦ (t j : F)) ht
      (LinearPlaneImage.coordinates (parameters I z u) (primitive I v) i) := by
    intro i
    rw [evaluation_coordinates I z u v w hw hwz, evaluation_coordinates I z u v t ht htz, hx, hy]
  have hh := PlaneImagePointSeparation.evaluations_equal_of_coordinates
    (parameters I z u) (primitive I v) hsource hfinite hprimitive
    (QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) hw)
    (QuotientPointEvaluation.evaluation I (fun i ↦ (t i : F)) ht) hcoords hδ
  have htow := QuotientPointEvaluation.points_equal I _ _ hw ht hh
  funext i
  exact Int.cast_injective (congrFun htow i)

end PaperP1.IntegerCurveProjectionCoordinates
