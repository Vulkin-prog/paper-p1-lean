module

public import PaperP1.Arithmetic.P3GraphPlaneNoetherTests
public import PaperP1.Arithmetic.P3GraphPlaneBadSectionCount
public import PaperP1.Algebra.P3GraphPlaneIrreducibilityCertificate

/-! # A literal nonzero Noether parameter polynomial is a finite-field section certificate

The hypothesis is an actual nonzero polynomial, rather than the desired surface
point estimate or an assumed geometric section. General existence of such a
certificate for every original geometrically irreducible surface remains open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneFiniteCertificate

open MvPolynomial PlaneHomogeneousCoefficientFamily P3GraphPlaneSection
open P3GraphPlaneNoetherTests P3GraphPlaneBadSectionCount
open scoped Classical

theorem bad_sections_bound {F : Type} [Field F] [Fintype F]
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms)
    (Φ : MvPolynomial (Index d) ℤ) (hΦ : Φ ∈ forms) (hne : test d P Φ ≠ 0) :
    (badSections P).card ≤ d * Φ.totalDegree * Fintype.card F ^ 2 := by
  have hroot : ∀ a ∈ badSections P, eval a (test d P Φ) = 0 := by
    intro a ha
    by_contra hn
    have hg := (geometric_section_iff (RingHom.id F) a d P hP forms hforms).mpr
      ⟨Φ, hΦ, by simpa only [coe_eval₂Hom, eval₂_id] using hn⟩
    exact (Finset.mem_filter.mp ha).2 (by simpa only [map_id] using hg)
  have hb := FiniteFieldPolynomialZeroBound.cardinality (by decide : 0 < 3)
    (test d P Φ) hne (badSections P) hroot
  have hd := P3GraphPlaneNoetherTests.degree_bound d P hP Φ
  simpa only [show (3 : ℕ) - 1 = 2 by decide] using
    hb.trans (Nat.mul_le_mul_right _ hd)

theorem exists_rational_section {F : Type} [Field F] [Fintype F]
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms)
    (Φ : MvPolynomial (Index d) ℤ) (hΦ : Φ ∈ forms) (hne : test d P Φ ≠ 0)
    (hlarge : d * Φ.totalDegree < Fintype.card F) :
    ∃ a : Fin 3 → F,
      Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)) :=
  exists_good_section P d Φ.totalDegree (bad_sections_bound d P hP forms hforms Φ hΦ hne) hlarge

theorem original_geometric_irreducible {F : Type} [Field F]
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms)
    (hnonzero : ∃ Φ ∈ forms, test d P Φ ≠ 0) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) P) := by
  obtain ⟨a, ha⟩ := (exists_closure_section_iff d P hP forms hforms).mpr hnonzero
  exact P3GraphPlaneIrreducibilityCertificate.geometric_irreducible_of_section P hP a ha

theorem uniform_rational_section_iff (d : ℕ) :
    ∃ (forms : Finset (MvPolynomial (Index d) ℤ)) (N : ℕ),
      PlaneUniversalNoetherForms.Valid d forms ∧
      ∀ (F : Type) [Field F] [Fintype F] (P : MvPolynomial (Fin 4) F),
        P.IsHomogeneous d → d * N < Fintype.card F →
        ((∃ a : Fin 3 → F,
          Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P))) ↔
          ∃ Φ ∈ forms, test d P Φ ≠ 0) := by
  obtain ⟨forms, hforms⟩ := PlaneUniversalNoetherForms.exists_forms d
  refine ⟨forms, IntegerPolynomialEvaluationMass.familyDegree forms, hforms, ?_⟩
  intro F _ _ P hP hlarge
  constructor
  · rintro ⟨a, ha⟩
    apply exists_nonzero_test_of_section (RingHom.id F) a d P hP forms hforms
    simpa only [map_id] using ha
  · rintro ⟨Φ, hΦ, hne⟩
    exact exists_rational_section d P hP forms hforms Φ hΦ hne
      (lt_of_le_of_lt (Nat.mul_le_mul_left d (Finset.le_sup hΦ)) hlarge)

end PaperP1.P3GraphPlaneFiniteCertificate
