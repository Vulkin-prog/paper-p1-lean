module

public import PaperP1.Geometry.IntegerCurveProjectionCoordinates
public import PaperP1.Geometry.LinearPlaneImageAffineEquation
public import PaperP1.Geometry.LinearPlaneImageBirational
public import PaperP1.Geometry.QuotientCurveSectionBudget

/-! # The actual original integer source population is bounded by its actual plane grid plus d(d-1) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurveProjectionCount

open MvPolynomial IntegerLinearPlaneProjection IntegerCurveProjectionCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime]
  [Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
  [IsScalarTower F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
  {K L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial (Fin 2) F) K] [Algebra K L]
  [Algebra (MvPolynomial (Fin n) F ⧸ I) L] [Algebra (MvPolynomial (Fin 2) F) L]
  [IsScalarTower (MvPolynomial (Fin 2) F) K L]
  [IsScalarTower (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) L]
  [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing (MvPolynomial (Fin n) F ⧸ I) L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem population (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (u v : Fin n → ℕ)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) =
      (aeval (R := F) (parameters I z u)).toRingHom)
    (hfinite : (aeval (R := F) (parameters I z u)).Finite)
    (hinj : Function.Injective (aeval (R := F) (parameters I z u)))
    (hrank : Module.finrank (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) = d)
    (hprimitive : IntermediateField.adjoin K
      {algebraMap (MvPolynomial (Fin n) F ⧸ I) L (primitive I v)} = ⊤)
    (B H : ℕ) (hu : ∀ i, u i ≤ B) (hv : ∀ i, v i ≤ B)
    (S : Finset (Fin n → ℤ)) (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    Irreducible (LinearPlaneImageAffineEquation.equation (F := F) (primitive I v)) ∧
      PlaneCurvePointCount.degree (LinearPlaneImageAffineEquation.equation (F := F) (primitive I v)) = d ∧
      S.card ≤ (PlaneCurvePointCount.grid
        (LinearPlaneImageAffineEquation.equation (F := F) (primitive I v)) (n * B * H)).card + (d - 1) * d := by
  classical
  let A := MvPolynomial (Fin n) F ⧸ I
  let H₀ := HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I
  let : GradedAlgebra H₀ := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin n) F) I hI
  let g := parameters I z u
  let y := primitive I v
  have hg : ∀ i, g i ∈ H₀ 1 := by
    intro i
    fin_cases i
    · exact Submodule.mem_map.mpr ⟨X z, isHomogeneous_X F z, rfl⟩
    · exact Submodule.mem_map.mpr ⟨_, CommonLinearNormalization.form_homogeneous _, rfl⟩
  have hy : y ∈ H₀ 1 :=
    Submodule.mem_map.mpr ⟨_, CommonLinearNormalization.form_homogeneous _, rfl⟩
  obtain ⟨b, himage⟩ := LinearPlaneImageBirational.exists_linear_hilbert g y K L H₀ hg hy
    hfinite hinj d hrank hsource hprimitive
  obtain ⟨hP, hdegree, _hmonic, hpoint⟩ :=
    LinearPlaneImageAffineEquation.properties H₀ g hg y hy hsource hfinite hinj d b himage
  have hmapinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) F) A) := by
    rw [hsource]
    exact hinj
  let : FaithfulSMul (MvPolynomial (Fin 2) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hmapinj
  let : Module.IsTorsionFree (MvPolynomial (Fin 2) F) A := inferInstance
  have hfin : Module.Finite (MvPolynomial (Fin 2) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfin
  have hint : IsIntegral (MvPolynomial (Fin 2) F) y := IsIntegral.of_finite _ y
  have hqhom : (LinearPlaneMinimalEquation.equation (F := F) y).IsHomogeneous d := by
    have hh := LinearPlaneMinimalEquation.equation_homogeneous H₀ g hg y hy hsource hint
    have he := LinearPlaneMinimalEquation.equation_totalDegree H₀ g hg y hy hsource hint
    have hD := LinearPlaneMinimalEquation.degree_of_image_hilbert H₀ g hg y hy hsource hint d b himage
    rw [← he, hD] at hh
    exact hh
  let δ := LinearPlaneImageFiber.denominator (F := F) y
  have hδhom : δ ∈ H₀ (d - 1) :=
    LinearPlaneImageFiber.denominator_homogeneous H₀ g hg y hy hsource d hqhom
  have hδ0 : δ ≠ 0 :=
    LinearPlaneImageFiber.denominator_ne_zero (K := K) (L := L) g y hsource hfinite
  obtain ⟨p, hphom, hpδ⟩ := Submodule.mem_map.mp hδhom
  change Ideal.Quotient.mk I p = δ at hpδ
  let Bad := S.filter (fun w ↦ eval (fun i ↦ (w i : F)) p = 0)
  let Good := S.filter (fun w ↦ eval (fun i ↦ (w i : F)) p ≠ 0)
  have hbad : Bad.card ≤ (d - 1) * d := by
    apply QuotientCurveSectionBudget.integer_population I hI inferInstance d hd b₀ hp δ hδhom hδ0 Bad z
      (fun w hw ↦ hnormal w (Finset.mem_filter.mp hw).1)
      (fun w hw ↦ hcurve w (Finset.mem_filter.mp hw).1)
    intro w hw
    rw [← hpδ, QuotientPointEvaluation.evaluation_mk]
    exact (Finset.mem_filter.mp hw).2
  have hgoodinj : Set.InjOn (projection u v) (↑Good : Set (Fin n → ℤ)) := by
    intro w hw t ht he
    have hwS := (Finset.mem_filter.mp hw).1
    have htS := (Finset.mem_filter.mp ht).1
    apply IntegerCurveProjectionCoordinates.points_equal I z u v hsource hfinite hprimitive w t
      (hcurve w hwS) (hcurve t htS) (hnormal w hwS) (hnormal t htS) he
    change QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hwS) δ ≠ 0
    rw [← hpδ, QuotientPointEvaluation.evaluation_mk]
    exact (Finset.mem_filter.mp hw).2
  let P := LinearPlaneImageAffineEquation.equation (F := F) y
  have hpoints : ∀ w ∈ S, P.evalEval (coordinate u w : F) (coordinate v w : F) = 0 := by
    intro w hw
    let φ := QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hw)
    have hnorm : φ (g 0) = 1 := by
      change QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hw)
        (Ideal.Quotient.mk I (X z)) = 1
      rw [QuotientPointEvaluation.evaluation_X, hnormal w hw, Int.cast_one]
    have hh := hpoint φ hnorm
    change P.evalEval
      (QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hw)
        (Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (u i : F)))))
      (QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hw)
        (Ideal.Quotient.mk I (CommonLinearNormalization.form (fun i ↦ (v i : F))))) = 0 at hh
    simpa only [quotient_evaluation] using hh
  have hsub : Good.image (projection u v) ⊆ PlaneCurvePointCount.grid P (n * B * H) := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    have hwS := (Finset.mem_filter.mp hw).1
    obtain ⟨hx, hy⟩ := projection_height u v hu hv w (hheight w hwS)
    apply (PlaneCurvePointCount.mem_grid P (n * B * H) _).mpr
    refine ⟨?_, ?_, hpoints w hwS⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hx
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hy
  have hgood : Good.card ≤ (PlaneCurvePointCount.grid P (n * B * H)).card := by
    rw [← Finset.card_image_of_injOn hgoodinj]
    exact Finset.card_le_card hsub
  have hpart : Bad.card + Good.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun w ↦ eval (fun i ↦ (w i : F)) p = 0)
  refine ⟨hP, hdegree, ?_⟩
  change S.card ≤ (PlaneCurvePointCount.grid P (n * B * H)).card + (d - 1) * d
  omega

end PaperP1.IntegerCurveProjectionCount
