module

public import PaperP1.Arithmetic.PlaneUniversalNoetherForms
public import PaperP1.Algebra.P3GraphPlaneSectionCoefficients
public import PaperP1.Algebra.IntegerFormPolynomialSubstitution
public import PaperP1.Algebra.IntegerPolynomialEvaluationMass
public import Mathlib.Algebra.MvPolynomial.Funext
public import PaperP1.Algebra.AlgClosedPolynomialIrreducibility

/-! # Literal parameter tests for actual geometric graph-plane sections

Nonvanishing of one test is equivalent to the existence of an actual section
over the algebraic closure. No assertion that a test is nonzero for every
geometrically irreducible original surface is made here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneNoetherTests

open MvPolynomial PlaneHomogeneousCoefficientFamily P3GraphPlaneSection
open P3GraphPlaneSectionCoefficients IntegerFormPolynomialSubstitution
open IntegerPolynomialEvaluationMass
open scoped Classical

variable {F : Type} [Field F]

def test (d : ℕ) (P : MvPolynomial (Fin 4) F) (Φ : MvPolynomial (Index d) ℤ) :
    MvPolynomial (Fin 3) F := substitute (coefficients d P) Φ

theorem degree_bound (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (Φ : MvPolynomial (Index d) ℤ) : (test d P Φ).totalDegree ≤ d * Φ.totalDegree :=
  IntegerFormPolynomialSubstitution.degree_bound (coefficients d P) d
    (P3GraphPlaneSectionCoefficients.degree_bound d P hP) Φ

theorem evaluation {K : Type} [Field K] (φ : F →+* K) (a : Fin 3 → K)
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (Φ : MvPolynomial (Index d) ℤ) :
    eval₂Hom φ a (test d P Φ) =
      eval (fun m : Index d ↦ (planeSection a (map φ P)).coeff m.val)
        (map (Int.castRingHom K) Φ) := by
  rw [test, natural]
  have he : (fun m ↦ eval₂Hom φ a (coefficients d P m)) =
      (fun m : Index d ↦ (planeSection a (map φ P)).coeff m.val) :=
    _root_.funext (specialized_coefficient φ a d P)
  rw [he]

theorem geometric_section_iff {K : Type} [Field K] (φ : F →+* K) (a : Fin 3 → K)
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms) :
    Irreducible (map (algebraMap K (AlgebraicClosure K)) (planeSection a (map φ P))) ↔
      ∃ Φ ∈ forms, eval₂Hom φ a (test d P Φ) ≠ 0 := by
  have hc := hforms K (fun m : Index d ↦ (planeSection a (map φ P)).coeff m.val)
  rw [PlaneHomogeneousReconstruction.reconstruct d _ (section_homogeneous a _ (hP.map φ))] at hc
  simpa only [evaluation] using hc

theorem exists_nonzero_test_of_section {K : Type} [Field K] (φ : F →+* K) (a : Fin 3 → K)
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms)
    (hgood : Irreducible (map (algebraMap K (AlgebraicClosure K)) (planeSection a (map φ P)))) :
    ∃ Φ ∈ forms, test d P Φ ≠ 0 := by
  obtain ⟨Φ, hΦ, hne⟩ := (geometric_section_iff φ a d P hP forms hforms).mp hgood
  refine ⟨Φ, hΦ, ?_⟩
  intro hz
  exact hne (by rw [hz, map_zero])

theorem exists_section_of_nonzero_test {K : Type} [Field K] [Infinite K]
    (φ : F →+* K) (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d)
    (forms : Finset (MvPolynomial (Index d) ℤ)) (hforms : PlaneUniversalNoetherForms.Valid d forms)
    (hnonzero : ∃ Φ ∈ forms, test d P Φ ≠ 0) :
    ∃ a : Fin 3 → K,
      Irreducible (map (algebraMap K (AlgebraicClosure K)) (planeSection a (map φ P))) := by
  obtain ⟨Φ, hΦ, hne⟩ := hnonzero
  have hm : map φ (test d P Φ) ≠ 0 := by
    intro hz
    exact hne (map_injective φ φ.injective (hz.trans (map_zero (MvPolynomial.map φ)).symm))
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → K, eval a (map φ (test d P Φ)) ≠ 0 := by
    by_contra! hall
    exact hm (MvPolynomial.funext (fun a ↦ by rw [hall a, map_zero]))
  refine ⟨a, (geometric_section_iff φ a d P hP forms hforms).mpr ⟨Φ, hΦ, ?_⟩⟩
  simpa only [eval_map, coe_eval₂Hom] using ha

theorem exists_closure_section_iff (d : ℕ) (P : MvPolynomial (Fin 4) F)
    (hP : P.IsHomogeneous d) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : PlaneUniversalNoetherForms.Valid d forms) :
    (∃ a : Fin 3 → AlgebraicClosure F,
      Irreducible (planeSection a (map (algebraMap F (AlgebraicClosure F)) P))) ↔
      ∃ Φ ∈ forms, test d P Φ ≠ 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact exists_nonzero_test_of_section (algebraMap F (AlgebraicClosure F)) a d P hP forms hforms
      (AlgClosedPolynomialIrreducibility.map_irreducible_iff _ |>.mpr ha)
  · intro hn
    obtain ⟨a, ha⟩ := exists_section_of_nonzero_test (algebraMap F (AlgebraicClosure F))
      d P hP forms hforms hn
    exact ⟨a, AlgClosedPolynomialIrreducibility.map_irreducible_iff _ |>.mp ha⟩

end PaperP1.P3GraphPlaneNoetherTests
