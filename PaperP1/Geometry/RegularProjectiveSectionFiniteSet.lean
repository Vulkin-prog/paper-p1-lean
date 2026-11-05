module

public import PaperP1.Geometry.RegularGradedSectionPoints

/-! # The complete actual projective section of a regular equation is finite without primality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularProjectiveSectionFiniteSet

open MvPolynomial ProjectiveSectionFiniteSet
attribute [local instance] MvPolynomial.gradedAlgebra

theorem card_bound {F A σ : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A] [Finite σ]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f))
    (S : Finset (Projectivization F (σ → F)))
    (hS : ∀ p ∈ S, p ∈ sectionLocus (GradedPolynomialPresentation.kernel (F := F) x) f) :
    S.card ≤ e * d := by
  classical
  let T := S.image (fun p ↦ p.rep)
  have hcard : T.card = S.card := Finset.card_image_of_injective _ rep_injective
  have hc := RegularGradedSectionPoints.projective_population H x hx hgen d hd b₀ hp f hf hregular T (by
    intro w hw
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hw
    exact p.rep_ne_zero) (by
    intro v hv w hw hrel
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨c, _hc, he⟩ := hrel
    have hproj : p = q := by
      have hh := (Projectivization.mk_eq_mk_iff' F p.rep q.rep p.rep_ne_zero q.rep_ne_zero).mpr
        ⟨c, funext (fun i ↦ (he i).symm)⟩
      simpa only [Projectivization.mk_rep] using hh
    exact congrArg (fun r : Projectivization F (σ → F) ↦ r.rep) hproj) (by
    intro w hw P hP
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hw
    exact (hS p hpS).1 P hP) (by
    intro w hw
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hw
    exact (hS p hpS).2)
  rw [hcard] at hc
  exact hc

theorem finite_locus {F A σ : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A] [Finite σ]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f)) :
    (sectionLocus (GradedPolynomialPresentation.kernel (F := F) x) f).Finite := by
  by_contra hbad
  have hinf : (sectionLocus (GradedPolynomialPresentation.kernel (F := F) x) f).Infinite := hbad
  obtain ⟨S, hS, hcard⟩ := hinf.exists_subset_card_eq (e * d + 1)
  have hc := card_bound H x hx hgen d hd b₀ hp f hf hregular S (fun _ hs ↦ hS hs)
  omega

theorem exists_finset {F A σ : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A] [Finite σ]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : σ → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f)) :
    ∃ E : Finset (Projectivization F (σ → F)),
      (∀ p, p ∈ E ↔ p ∈ sectionLocus (GradedPolynomialPresentation.kernel (F := F) x) f) ∧
        E.card ≤ e * d := by
  classical
  have hfinite := finite_locus H x hx hgen d hd b₀ hp f hf hregular
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · exact fun _ ↦ hfinite.mem_toFinset
  · exact card_bound H x hx hgen d hd b₀ hp f hf hregular _ (fun _ hp ↦ hfinite.mem_toFinset.mp hp)

end PaperP1.RegularProjectiveSectionFiniteSet
