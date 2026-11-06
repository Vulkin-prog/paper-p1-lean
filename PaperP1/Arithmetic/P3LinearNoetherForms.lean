module

public import PaperP1.Arithmetic.P3UniversalNoetherForms
public import PaperP1.Arithmetic.P3CertificateFromNoetherForms
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! # Explicit universal integer Noether forms in degree one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3LinearNoetherForms

open MvPolynomial Finset P3HomogeneousCoefficientFamily
open scoped Classical

def forms : Finset (MvPolynomial (Index 1) ℤ) :=
  (univ : Finset (Index 1)).image (fun m ↦ X m)

theorem valid : P3UniversalNoetherForms.Valid 1 forms := by
  intro F _inst a
  constructor
  · intro hirr
    have ha : ∃ m, a m ≠ 0 := by
      by_contra hn
      have hz : a = 0 := by
        funext m
        exact Classical.not_not.mp (fun hm ↦ hn ⟨m, hm⟩)
      have hp : polynomial 1 a = 0 := by simp only [hz, polynomial, Pi.zero_apply, monomial_zero, sum_const_zero]
      exact hirr.ne_zero (by rw [hp, map_zero])
    obtain ⟨m, hm⟩ := ha
    refine ⟨X m, mem_image.mpr ⟨m, mem_univ _, rfl⟩, ?_⟩
    simpa only [map_X, eval_X] using hm
  · rintro ⟨Φ, hΦ, hΦzero⟩
    obtain ⟨m, _, rfl⟩ := mem_image.mp hΦ
    have hm : a m ≠ 0 := by simpa only [map_X, eval_X] using hΦzero
    have ha : a ≠ 0 := fun hz ↦ hm (congrFun hz m)
    have hP0 : polynomial 1 a ≠ 0 := nonzero 1 a ha
    have hmap0 : map (algebraMap F (AlgebraicClosure F)) (polynomial 1 a) ≠ 0 := by
      intro hz
      apply hP0
      exact map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
        (hz.trans (map_zero _).symm)
    have hhom : (map (algebraMap F (AlgebraicClosure F)) (polynomial 1 a)).IsHomogeneous 1 :=
      (homogeneous 1 a).map _
    apply irreducible_of_totalDegree_eq_one (hhom.totalDegree hmap0)
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hxzero
    apply hmap0
    ext u
    have hh := hx u
    rw [hxzero] at hh
    simpa using zero_dvd_iff.mp hh

theorem exists_forms : P3UniversalNoetherForms.ExistsForms 1 := ⟨forms, valid⟩

theorem card_forms : forms.card = 4 := by
  rw [forms, Finset.card_image_of_injective _ X_injective, card_univ, index_card]
  norm_num

theorem uniform_auxiliary_one : UniformP3AuxiliaryHypersurface.UniformAuxiliary 1 :=
  P3CertificateFromNoetherForms.uniform_auxiliary 1 exists_forms
    (P3FiniteFieldClassEstimate.of_degree_le_one 1 le_rfl)

end PaperP1.P3LinearNoetherForms
