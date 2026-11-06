module

public import PaperP1.Arithmetic.P3UniversalNoetherFormsExistence
public import PaperP1.Algebra.PlaneToP3CoefficientExtension
public import PaperP1.Algebra.IrreducibleVariableExtension

/-! # Actual universal integer Noether forms for plane curves in every degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneUniversalNoetherForms

open MvPolynomial PlaneHomogeneousCoefficientFamily PlaneToP3CoefficientExtension
open scoped Classical

def Valid (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ)) : Prop :=
  ∀ (F : Type) [Field F] (a : Index d → F),
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (polynomial d a)) ↔
      ∃ Φ ∈ forms, eval a (map (Int.castRingHom F) Φ) ≠ 0

def ExistsForms (d : ℕ) : Prop := ∃ forms : Finset (MvPolynomial (Index d) ℤ), Valid d forms

theorem valid_pullback (d : ℕ) (forms : Finset (MvPolynomial (P3HomogeneousCoefficientFamily.Index d) ℤ))
    (hforms : P3UniversalNoetherForms.Valid d forms) : Valid d (forms.image (pullback d)) := by
  intro F _ a
  let b : P3HomogeneousCoefficientFamily.Index d → F := fun m ↦
    (rename Fin.succ (polynomial d a)).coeff m.val
  have he : map (algebraMap F (AlgebraicClosure F)) (P3HomogeneousCoefficientFamily.polynomial d b) =
      rename Fin.succ (map (algebraMap F (AlgebraicClosure F)) (polynomial d a)) := by
    rw [reconstruct_extended, map_rename]
  have hi : Irreducible (map (algebraMap F (AlgebraicClosure F))
      (P3HomogeneousCoefficientFamily.polynomial d b)) ↔
      Irreducible (map (algebraMap F (AlgebraicClosure F)) (polynomial d a)) := by
    rw [he]
    exact IrreducibleVariableExtension.irreducible_rename Fin.succ (Fin.succ_injective 3) _
  constructor
  · intro hirr
    obtain ⟨Φ, hΦ, hne⟩ := (hforms F b).mp (hi.mpr hirr)
    refine ⟨pullback d Φ, Finset.mem_image.mpr ⟨Φ, hΦ, rfl⟩, ?_⟩
    rw [evaluate_pullback]
    exact hne
  · rintro ⟨Φ, hΦ, hne⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := Finset.mem_image.mp hΦ
    apply hi.mp
    apply (hforms F b).mpr
    refine ⟨Ψ, hΨ, ?_⟩
    rw [evaluate_pullback] at hne
    exact hne

theorem exists_forms (d : ℕ) : ExistsForms d := by
  obtain ⟨forms, hforms⟩ := P3UniversalNoetherFormsExistence.exists_forms d
  exact ⟨forms.image (pullback d), valid_pullback d forms hforms⟩

end PaperP1.PlaneUniversalNoetherForms
