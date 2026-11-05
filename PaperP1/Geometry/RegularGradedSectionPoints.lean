module

public import PaperP1.Algebra.RegularGradedHilbertSection
public import PaperP1.Algebra.GradedPolynomialPresentation
public import PaperP1.Algebra.LinearNormalizedPointEvaluation
public import PaperP1.Geometry.QuotientPointEvaluation
public import PaperP1.Geometry.ProjectiveSectionFiniteSet

/-! # Actual regular sections of any generated graded curve algebra have the genuine degree budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularGradedSectionPoints

open MvPolynomial CommonLinearNormalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem linear_population {F A σ : Type*} [Field F] [CommRing A] [Algebra F A] [Finite σ]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f))
    (S : Finset (σ → F)) (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (hnormal : ∀ w ∈ S, eval w ℓ = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ GradedPolynomialPresentation.kernel (F := F) x, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * d := by
  classical
  let J := GradedPolynomialPresentation.kernel (F := F) x
  let E := GradedPolynomialPresentation.toSource H x hx hgen
  let evJ : S → (MvPolynomial σ F ⧸ J) →ₐ[F] F := fun w ↦
    QuotientPointEvaluation.evaluation J w.val (hcurve w.val w.property)
  let evA : S → A →ₐ[F] F := fun w ↦ (evJ w).comp E.symm.toAlgHom
  have heval (w : S) (p : MvPolynomial σ F) : evA w (aeval x p) = eval w.val p := by
    change evJ w (E.symm (aeval x p)) = eval w.val p
    have hmap : E (Ideal.Quotient.mk J p) = aeval x p :=
      GradedPolynomialPresentation.toSource_mk H x hx hgen p
    rw [← hmap, E.symm_apply_apply]
    rfl
  let b := aeval x f
  have hb : b ∈ H e := GradedPolynomialGenerators.eval_homogeneous H x hx e f hf
  let K := HomogeneousPrincipalQuotient.ideal b
  have hevA (w : S) : evA w b = 0 := (heval w f).trans (hsection w.val w.property)
  have hK (w : S) : ∀ a ∈ K, evA w a = 0 := by
    have hle : K ≤ RingHom.ker (evA w).toRingHom := by
      change Ideal.span {b} ≤ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact hevA w
    exact fun _ ha ↦ hle ha
  let ev : S → (A ⧸ K) →ₐ[F] F := fun w ↦ Ideal.Quotient.liftₐ K (evA w) (hK w)
  let q : MvPolynomial σ F →ₐ[F] A ⧸ K := (Ideal.Quotient.mkₐ F K).comp (aeval x)
  have hcompat : ∀ p : MvPolynomial σ F, ∀ w : S, ev w (q p) = eval w.val p := by
    intro p w
    exact heval w p
  obtain ⟨N, hN⟩ := RegularGradedHilbertSection.eventual_dimension H d hd b₀ hp hb hregular
  let r := max N S.card
  have hc := LinearNormalizedPointEvaluation.card_le_dimension S ℓ hℓ hnormal (r + e)
    (by dsimp [r]; omega) q ev hcompat
  have hpiece : (homogeneousSubmodule σ F (r + e)).map q.toLinearMap =
      HomogeneousPrincipalQuotient.piece H b (r + e) := by
    apply le_antisymm
    · rintro a ⟨p, hp, rfl⟩
      exact Submodule.mem_map.mpr ⟨aeval x p,
        GradedPolynomialGenerators.eval_homogeneous H x hx (r + e) p hp, rfl⟩
    · rintro a ⟨v, hv, he⟩
      obtain ⟨p, hp, hpv⟩ := GradedSurjectiveChartMap.homogeneous_preimage
        (GradedPolynomialGenerators.gradedEval H x hx)
        (GradedPolynomialGenerators.eval_surjective H x hx hgen) (r + e) v hv
      refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
      change Ideal.Quotient.mk K (aeval x p) = a
      change aeval x p = v at hpv
      rw [hpv]
      exact he
  rw [hpiece] at hc
  exact hc.trans_eq (hN r (le_max_left _ _))

theorem projective_population {F A σ : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A] [Finite σ]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f))
    (S : Finset (σ → F)) (hne : ∀ w ∈ S, w ≠ 0)
    (hsep : ∀ v ∈ S, ∀ w ∈ S, (∃ c : F, c ≠ 0 ∧ ∀ i, v i = c * w i) → v = w)
    (hcurve : ∀ w ∈ S, ∀ P ∈ GradedPolynomialPresentation.kernel (F := F) x, eval w P = 0)
    (hsection : ∀ w ∈ S, eval w f = 0) : S.card ≤ e * d := by
  classical
  obtain ⟨ℓ, hℓ, hnonzero⟩ := exists_form S hne
  let T := S.image (normalize ℓ)
  have hcard : T.card = S.card := Finset.card_image_of_injOn (normalize_injOn S ℓ hnonzero hsep)
  have hnormal : ∀ w ∈ T, eval w ℓ = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact normalized_value ℓ hℓ v (hnonzero v hv)
  have hJ := GradedPolynomialPresentation.kernel_homogeneous H x hx
  have hcurveT : ∀ w ∈ T, ∀ P ∈ GradedPolynomialPresentation.kernel (F := F) x, eval w P = 0 := by
    intro w hw P hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact HomogeneousIdealPointScaling.zeros_scale _ hJ v (hcurve v hv) (eval v ℓ)⁻¹ P hP
  have hsectionT : ∀ w ∈ T, eval w f = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    change eval (fun i ↦ (eval v ℓ)⁻¹ * v i) f = 0
    rw [HomogeneousPolynomialEvaluation.eval_scale f hf, hsection v hv, mul_zero]
  have hc := linear_population H x hx hgen d hd b₀ hp f hf hregular T ℓ hℓ hnormal hcurveT hsectionT
  rw [hcard] at hc
  exact hc

end PaperP1.RegularGradedSectionPoints
