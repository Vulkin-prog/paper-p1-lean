module

public import PaperP1.Geometry.RegularProjectiveSectionFiniteSet
public import PaperP1.Algebra.BoundedMomentLinearForm
public import PaperP1.Algebra.ProjectiveAvoidanceRadical
public import Mathlib.Algebra.CharZero.Infinite

/-! # Bounded integer forms avoid the whole actual regular section and force actual coordinate powers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedRegularSectionAvoidance

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_coefficients {F A : Type*} [Field F] [CharZero F] [CommRing A] [Algebra F A] (n : ℕ)
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : Fin n → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f)) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * (e * d) + 1) ^ (n - 1)) ∧
      ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus (GradedPolynomialPresentation.kernel (F := F) x) f,
        eval p.rep (CommonLinearNormalization.form (fun i ↦ (u i : F))) ≠ 0 := by
  classical
  obtain ⟨E, hE, hcard⟩ := RegularProjectiveSectionFiniteSet.exists_finset H x hx hgen d hd b₀ hp f hf hregular
  let S := E.image (fun p ↦ p.rep)
  have hS : S.card ≤ e * d := by
    change (E.image (fun p ↦ p.rep)).card ≤ _
    rw [Finset.card_image_of_injective _ ProjectiveSectionFiniteSet.rep_injective]
    exact hcard
  obtain ⟨u, hu, hnonzero⟩ := BoundedMomentLinearForm.exists_coefficients n S (by
    intro w hw
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hw
    exact p.rep_ne_zero)
  refine ⟨u, ?_, ?_⟩
  · intro i
    apply (hu i).trans
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (n - 1) hS) 1
  · intro p hpsection
    exact hnonzero p.rep (Finset.mem_image.mpr ⟨p, (hE p).mpr hpsection, rfl⟩)

theorem exists_coefficients_powers {F A : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    [CommRing A] [Algebra F A] (n : ℕ)
    (H : ℕ → Submodule F A) [GradedAlgebra H] (x : Fin n → A) (hx : ∀ i, x i ∈ H 1)
    (hgen : Algebra.adjoin F (Set.range x) = ⊤) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial (Fin n) F) (hf : f.IsHomogeneous e)
    (hregular : Function.Injective (fun a : A ↦ a * aeval x f)) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * (e * d) + 1) ^ (n - 1)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ i : Fin n, (X i) ^ N ∈
        GradedPolynomialPresentation.kernel (F := F) x ⊔
          Ideal.span {f, CommonLinearNormalization.form (fun i ↦ (u i : F))} := by
  obtain ⟨u, hu, havoid⟩ := exists_coefficients n H x hx hgen d hd b₀ hp f hf hregular
  obtain ⟨N, hN, hpow⟩ := ProjectiveAvoidanceRadical.exists_uniform_power
    (GradedPolynomialPresentation.kernel (F := F) x)
    (GradedPolynomialPresentation.kernel_homogeneous H x hx) f hf
    (CommonLinearNormalization.form (fun i ↦ (u i : F))) (CommonLinearNormalization.form_homogeneous _) havoid
  exact ⟨u, hu, N, hN, hpow⟩

end PaperP1.BoundedRegularSectionAvoidance
