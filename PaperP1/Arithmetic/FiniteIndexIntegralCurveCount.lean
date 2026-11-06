module

public import PaperP1.Arithmetic.UniformIntegralCurveCount
public import PaperP1.Algebra.GradedPolynomialPresentation
public import PaperP1.Geometry.QuotientPointEvaluation

/-! # The actual integer curve bound is independent of the chosen finite coordinate index type -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteIndexIntegralCurveCount

universe u

open MvPolynomial QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

theorem population_bound {F : Type u} [Field F] [CharZero F] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : σ) (H : ℕ) (hH : 1 ≤ H) (S : Finset (σ → ℤ))
    (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    (S.card : ℝ) ≤ UniformIntegralCurveCount.constant.{u} (Nat.card σ) * profile d H := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : I.IsPrime := hprime
  let n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let A := MvPolynomial σ F ⧸ I
  let G := HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I
  let : GradedAlgebra G := HomogeneousQuotientGrading.grading (homogeneousSubmodule σ F) I hI
  let x : Fin n → A := fun i ↦ Ideal.Quotient.mk I (X (e.symm i))
  have hx : ∀ i, x i ∈ G 1 := fun i ↦
    Submodule.mem_map.mpr ⟨X (e.symm i), isHomogeneous_X F (e.symm i), rfl⟩
  have hgen : Algebra.adjoin F (Set.range x) = ⊤ := by
    have he : Set.range x = Set.range (fun i : σ ↦ Ideal.Quotient.mk I (X i)) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [x]⟩
    rw [he]
    exact CoordinateFractionFieldGenerators.quotient_variables_generate I
  let J := GradedPolynomialPresentation.kernel (F := F) x
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin n) F) :=
    GradedPolynomialPresentation.kernel_homogeneous G x hx
  have hJprime : J.IsPrime := RingHom.ker_isPrime (aeval (R := F) x)
  have hpJ : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) J)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀) := by
    obtain ⟨N, hN⟩ := hp
    refine ⟨N, fun r hr ↦ ?_⟩
    have he : Module.finrank F (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) J r) =
        Module.finrank F (G r) := (GradedPolynomialPresentation.pieceEquiv G x hx hgen r).finrank_eq
    rw [he]
    exact hN r hr
  let c : (σ → ℤ) → Fin n → ℤ := fun w i ↦ w (e.symm i)
  have hinj : Function.Injective c := by
    intro w v he
    funext i
    have hh := congrFun he (e i)
    simpa only [c, e.symm_apply_apply] using hh
  let T := S.image c
  have hcard : T.card = S.card := Finset.card_image_of_injective _ hinj
  have hnormalT : ∀ w ∈ T, w (e z) = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    change v (e.symm (e z)) = 1
    rw [e.symm_apply_apply]
    exact hnormal v hv
  have hcurveT : ∀ w ∈ T, ∀ P ∈ J, eval (fun i ↦ (w i : F)) P = 0 := by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    let φ := QuotientPointEvaluation.evaluation I (fun i ↦ (v i : F)) (hcurve v hv)
    have hp0 : aeval (R := F) x P = 0 := hP
    have hh := congrArg φ hp0
    rw [map_zero, comp_aeval_apply] at hh
    change eval (fun j ↦ φ (x j)) P = 0 at hh
    have he : (fun j ↦ φ (x j)) = (fun j ↦ (c v j : F)) := by
      funext j
      exact QuotientPointEvaluation.evaluation_X I (fun i ↦ (v i : F)) (hcurve v hv) (e.symm j)
    rwa [he] at hh
  have hheightT : ∀ w ∈ T, ∀ i, (w i).natAbs ≤ H := by
    intro w hw i
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hheight v hv (e.symm i)
  have hc := UniformIntegralCurveCount.population_bound n J hJ hJprime d hd b₀ hpJ (e z) H hH T
    hnormalT hcurveT hheightT
  rw [hcard] at hc
  simpa only [Nat.card_eq_fintype_card] using hc

end PaperP1.FiniteIndexIntegralCurveCount
