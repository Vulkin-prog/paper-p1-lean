module

public import PaperP1.Geometry.QuotientPointEvaluation
public import PaperP1.Geometry.ProjectiveHomogeneousSectionPoints
public import Mathlib.Data.Int.Cast.Field

/-! # Actual quotient-section zeros have the original curve degree budget, including integer populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuotientCurveSectionBudget

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalized_population {F σ : Type*} [Field F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (δ : MvPolynomial σ F ⧸ I)
    (hδ : δ ∈ HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I e) (hδ0 : δ ≠ 0)
    (S : Finset (σ → F)) (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (hnormal : ∀ w ∈ S, eval w ℓ = 1) (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval w P = 0)
    (hzero : ∀ w (hw : w ∈ S), QuotientPointEvaluation.evaluation I w (hcurve w hw) δ = 0) :
    S.card ≤ e * d := by
  obtain ⟨p, hphom, he⟩ := Submodule.mem_map.mp hδ
  change Ideal.Quotient.mk I p = δ at he
  have hnot : p ∉ I := by
    intro hpI
    apply hδ0
    rw [← he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  apply ProjectiveHomogeneousSectionPoints.linear_normalized_population
    I hI hprime d hd b₀ hp p hphom hnot S ℓ hℓ hnormal hcurve
  intro w hw
  have hh := hzero w hw
  rwa [← he, QuotientPointEvaluation.evaluation_mk] at hh

theorem integer_population {F σ : Type*} [Field F] [CharZero F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (δ : MvPolynomial σ F ⧸ I)
    (hδ : δ ∈ HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I e) (hδ0 : δ ≠ 0)
    (S : Finset (σ → ℤ)) (z : σ) (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hzero : ∀ w (hw : w ∈ S),
      QuotientPointEvaluation.evaluation I (fun i ↦ (w i : F)) (hcurve w hw) δ = 0) : S.card ≤ e * d := by
  classical
  let c : (σ → ℤ) → σ → F := fun w i ↦ (w i : F)
  have hinj : Function.Injective c := by
    intro v w he
    funext i
    exact Int.cast_injective (congrFun he i)
  let T := S.image c
  have hcurveT : ∀ w ∈ T, ∀ P ∈ I, eval w P = 0 := by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hcurve v hv P hP
  have hc := normalized_population I hI hprime d hd b₀ hp δ hδ hδ0 T (X z) (isHomogeneous_X F z) (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [eval_X]
    change (v z : F) = 1
    rw [hnormal v hv, Int.cast_one]) hcurveT (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hzero v hv)
  change (S.image c).card ≤ e * d at hc
  rw [Finset.card_image_of_injective _ hinj] at hc
  exact hc

end PaperP1.QuotientCurveSectionBudget
