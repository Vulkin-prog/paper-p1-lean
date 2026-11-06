module

public import PaperP1.Algebra.P3CoefficientMultiplication
public import PaperP1.Algebra.HomogeneousQuotientGrading

/-! # The actual universal integer rank-one coefficient relations for polynomial multiplication -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegreRelations

open MvPolynomial Finset P3HomogeneousCoefficientFamily
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Coords (e f : ℕ) := Index e × Index f

abbrev Ring (e f : ℕ) := MvPolynomial (Coords e f) ℤ

def relation (e f : ℕ) (i k : Index e) (j l : Index f) : Ring e f :=
  X (i, j) * X (k, l) - X (i, l) * X (k, j)

def relations (e f : ℕ) : Finset (Ring e f) :=
  (univ : Finset ((Index e × Index e) × (Index f × Index f))).image
    (fun t ↦ relation e f t.1.1 t.1.2 t.2.1 t.2.2)

def ideal (e f : ℕ) : Ideal (Ring e f) := Ideal.span (relations e f : Set (Ring e f))

theorem relation_homogeneous (e f : ℕ) (i k : Index e) (j l : Index f) :
    (relation e f i k j l).IsHomogeneous 2 :=
  ((isHomogeneous_X ℤ (i, j)).mul (isHomogeneous_X ℤ (k, l))).sub
    ((isHomogeneous_X ℤ (i, l)).mul (isHomogeneous_X ℤ (k, j)))

theorem relation_mem (e f : ℕ) (i k : Index e) (j l : Index f) :
    relation e f i k j l ∈ ideal e f := by
  apply Ideal.subset_span
  exact mem_image.mpr ⟨((i, k), (j, l)), mem_univ _, rfl⟩

theorem ideal_homogeneous (e f : ℕ) :
    (ideal e f).IsHomogeneous (homogeneousSubmodule (Coords e f) ℤ) := by
  apply Ideal.homogeneous_span
  intro P hP
  obtain ⟨t, _, rfl⟩ := mem_image.mp hP
  exact ⟨2, relation_homogeneous e f t.1.1 t.1.2 t.2.1 t.2.2⟩

theorem pure_tensor_vanishes {F : Type*} [CommRing F] (e f : ℕ)
    (a : Index e → F) (b : Index f → F) (i k : Index e) (j l : Index f) :
    eval (fun ij ↦ a ij.1 * b ij.2) (map (Int.castRingHom F) (relation e f i k j l)) = 0 := by
  simp only [relation, map_sub, map_mul, map_X, eval_X]
  ring

theorem vanishing_iff_rank_one {F : Type*} [CommRing F] (e f : ℕ) (z : Coords e f → F) :
    (∀ P ∈ relations e f, eval z (map (Int.castRingHom F) P) = 0) ↔
      ∀ (i k : Index e) (j l : Index f), z (i, j) * z (k, l) = z (i, l) * z (k, j) := by
  constructor
  · intro h i k j l
    have hh := h (relation e f i k j l) (mem_image.mpr ⟨((i, k), (j, l)), mem_univ _, rfl⟩)
    simpa only [relation, map_sub, map_mul, map_X, eval_X, sub_eq_zero] using hh
  · intro h P hP
    obtain ⟨t, _, rfl⟩ := mem_image.mp hP
    simp only [relation, map_sub, map_mul, map_X, eval_X, h, sub_self]

end PaperP1.P3FactorSegreRelations
