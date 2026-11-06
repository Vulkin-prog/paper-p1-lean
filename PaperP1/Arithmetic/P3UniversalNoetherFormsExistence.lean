module

public import PaperP1.Arithmetic.P3UniversalNoetherForms
public import PaperP1.Geometry.P3FactorLocusIrreducibility

/-! # Finite universal integer Noether forms in every degree, with the exact all-fields criterion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3UniversalNoetherFormsExistence

open MvPolynomial P3HomogeneousCoefficientFamily
open scoped Classical

theorem exists_forms_positive (d : ℕ) (hd : 0 < d) : P3UniversalNoetherForms.ExistsForms d := by
  obtain ⟨forms, _hhom, hforms, hzero⟩ := P3ProjectiveFactorLocus.finite_positive_equations d
  refine ⟨forms, ?_⟩
  intro F _ a
  by_cases ha : a = 0
  · constructor
    · intro hirr
      apply False.elim
      apply hirr.ne_zero
      simp only [ha, polynomial, Pi.zero_apply, Finset.sum_const_zero, map_zero]
    · rintro ⟨Φ, hΦ, hne⟩
      apply False.elim
      apply hne
      rw [ha]
      exact hzero F Φ hΦ
  · let φ := algebraMap F (AlgebraicClosure F)
    let a' := φ ∘ a
    have ha' : a' ≠ 0 := IntegerCoefficientProjectivePoint.map_vector_ne_zero φ a ha
    have hp : map φ (polynomial d a) = polynomial d a' := P3CoefficientFieldTransport.map_polynomial φ d a
    have he : IntegerCoefficientProjectivePoint.point a' ha' = IntegerCoefficientProjectivePoint.point a ha :=
      IntegerCoefficientProjectivePoint.point_map φ a ha
    have hc : (¬ Irreducible (map φ (polynomial d a))) ↔
        ∀ Φ ∈ forms, eval a (map (Int.castRingHom F) Φ) = 0 := by
      rw [hp, ← P3FactorLocusIrreducibility.mem_iff_not_irreducible d hd a' ha', he]
      exact hforms F a ha
    constructor
    · intro hirr
      have hn : ¬ (∀ Φ ∈ forms, eval a (map (Int.castRingHom F) Φ) = 0) :=
        fun hh ↦ hc.mpr hh hirr
      push Not at hn
      exact hn
    · rintro ⟨Φ, hΦ, hne⟩
      by_contra hirr
      exact hne (hc.mp hirr Φ hΦ)

theorem exists_forms_zero : P3UniversalNoetherForms.ExistsForms 0 := by
  refine ⟨∅, ?_⟩
  intro F _ a
  constructor
  · intro hirr
    have hh := (homogeneous 0 a).map (algebraMap F (AlgebraicClosure F))
    have hu := P3FactorLocusIrreducibility.zero_degree_unit _ hirr.ne_zero (hh.totalDegree hirr.ne_zero)
    exact False.elim (hirr.not_isUnit hu)
  · rintro ⟨Φ, hΦ, _⟩
    simp at hΦ

theorem exists_forms (d : ℕ) : P3UniversalNoetherForms.ExistsForms d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact exists_forms_zero
  · exact exists_forms_positive d hd

end PaperP1.P3UniversalNoetherFormsExistence
