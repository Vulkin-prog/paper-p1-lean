module

public import PaperP1.Geometry.ProjectiveCurveHilbertDegree
public import PaperP1.Algebra.LinearNormalizedPointEvaluation
public import PaperP1.Algebra.CommonLinearNormalization
public import PaperP1.Algebra.HomogeneousIdealPointScaling

/-! # A genuine chart-independent homogeneous section count over any infinite field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveHomogeneousSectionPoints

open MvPolynomial CommonLinearNormalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem linear_normalized_population {F σ : Type*} [Field F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (hnot : f ∉ I)
    (S : Finset (σ → F)) (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (hnormal : ∀ w ∈ S, eval w ℓ = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * d := by
  classical
  let : I.IsPrime := hprime
  let A := (MvPolynomial σ F) ⧸ I
  let G : ℕ → Submodule F A := HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I
  let : GradedAlgebra G := HomogeneousQuotientGrading.grading (homogeneousSubmodule σ F) I hI
  let b : A := Ideal.Quotient.mk I f
  have hb : b ∈ G e := Submodule.mem_map.mpr ⟨f, hf, rfl⟩
  have hb0 : b ≠ 0 := fun he ↦ hnot (Ideal.Quotient.eq_zero_iff_mem.mp he)
  let J := HomogeneousPrincipalQuotient.ideal b
  let B := A ⧸ J
  let q : MvPolynomial σ F →ₐ[F] B := (Ideal.Quotient.mkₐ F J).comp (Ideal.Quotient.mkₐ F I)
  let evI : S → A →ₐ[F] F := fun w ↦ Ideal.Quotient.liftₐ I (MvPolynomial.aeval w.val)
    (fun P hP ↦ hcurve w.val w.property P hP)
  have hevI (w : S) : evI w b = 0 := hsection w.val w.property
  have hJ (w : S) : ∀ x ∈ J, evI w x = 0 := by
    have hle : J ≤ RingHom.ker (evI w).toRingHom := by
      change Ideal.span {b} ≤ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact hevI w
    exact fun _ hx ↦ hle hx
  let ev : S → B →ₐ[F] F := fun w ↦ Ideal.Quotient.liftₐ J (evI w) (hJ w)
  have hcompat : ∀ P : MvPolynomial σ F, ∀ w : S, ev w (q P) = eval w.val P := by
    intro P w
    rfl
  obtain ⟨N, hN⟩ := GradedLinearHilbertSection.eventual_dimension G d hd b₀ hp hb hb0
  let n := max N S.card
  have hc := LinearNormalizedPointEvaluation.card_le_dimension S ℓ hℓ hnormal (n + e)
    (by dsimp [n]; omega) q ev hcompat
  have hpiece : (homogeneousSubmodule σ F (n + e)).map q.toLinearMap =
      HomogeneousPrincipalQuotient.piece G b (n + e) := by
    change _ = ((homogeneousSubmodule σ F (n + e)).map
      (Ideal.Quotient.mkₐ F I).toLinearMap).map (Ideal.Quotient.mkₐ F J).toLinearMap
    rw [← Submodule.map_comp]
    rfl
  rw [hpiece] at hc
  exact hc.trans_eq (hN n (le_max_left _ _))

theorem projective_population {F σ : Type*} [Field F] [Infinite F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (hnot : f ∉ I)
    (S : Finset (σ → F)) (hne : ∀ w ∈ S, w ≠ 0)
    (hsep : ∀ v ∈ S, ∀ w ∈ S, (∃ c : F, c ≠ 0 ∧ ∀ i, v i = c * w i) → v = w)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * d := by
  classical
  obtain ⟨ℓ, hℓ, hnonzero⟩ := exists_form S hne
  let T := S.image (normalize ℓ)
  have hcard : T.card = S.card := Finset.card_image_of_injOn (normalize_injOn S ℓ hnonzero hsep)
  have hnormal : ∀ w ∈ T, eval w ℓ = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact normalized_value ℓ hℓ v (hnonzero v hv)
  have hcurveT : ∀ w ∈ T, ∀ P ∈ I, eval w P = 0 := by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact HomogeneousIdealPointScaling.zeros_scale I hI v (hcurve v hv) (eval v ℓ)⁻¹ P hP
  have hsectionT : ∀ w ∈ T, eval w f = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    change eval (fun i ↦ (eval v ℓ)⁻¹ * v i) f = 0
    rw [HomogeneousPolynomialEvaluation.eval_scale f hf, hsection v hv, mul_zero]
  have hc := linear_normalized_population I hI hprime d hd b₀ hp f hf hnot T ℓ hℓ hnormal hcurveT hsectionT
  rw [hcard] at hc
  exact hc

theorem rational_curve_population {σ : Type} [Finite σ] (Γ : ProjectiveCurveData.Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal)
    (S : Finset (σ → ℚ)) (hne : ∀ w ∈ S, w ≠ 0)
    (hsep : ∀ v ∈ S, ∀ w ∈ S, (∃ c : ℚ, c ≠ 0 ∧ ∀ i, v i = c * w i) → v = w)
    (hcurve : ∀ w ∈ S, ∀ P ∈ Γ.ideal, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * ProjectiveCurveHilbertDegree.natDegree Γ := by
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial (ProjectiveCurveData.piece Γ.ideal)
      (Polynomial.C (ProjectiveCurveHilbertDegree.natDegree Γ : ℚ) * Polynomial.X + Polynomial.C Γ.constant) := by
    rw [ProjectiveCurveHilbertDegree.natDegree_cast Γ]
    exact Γ.hilbert
  exact projective_population Γ.ideal Γ.homogeneous Γ.prime _ (ProjectiveCurveHilbertDegree.natDegree_pos Γ)
    Γ.constant hp f hf hnot S hne hsep hcurve hsection

end PaperP1.ProjectiveHomogeneousSectionPoints
