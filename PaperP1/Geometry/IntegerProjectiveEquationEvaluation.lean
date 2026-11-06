module

public import PaperP1.Geometry.IntegerCoefficientProjectivePoint
public import PaperP1.Geometry.ProjectiveIntegerClosedEquations

/-! # Finite projective equations evaluated on actual field-valued coefficient vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerProjectiveEquationEvaluation

open MvPolynomial Finset IntegerCoefficientProjectivePoint
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type} [Fintype σ]

def positiveForms (forms : Finset (MvPolynomial σ ℤ)) : Finset (MvPolynomial σ ℤ) :=
  forms.biUnion (fun P ↦ univ.image (fun i ↦ P * X i))

theorem positive_homogeneous (forms : Finset (MvPolynomial σ ℤ))
    (hforms : ∀ P ∈ forms, ∃ n : ℕ, P.IsHomogeneous n) :
    ∀ P ∈ positiveForms forms, ∃ n : ℕ, 0 < n ∧ P.IsHomogeneous n := by
  intro P hP
  obtain ⟨Q, hQ, hP⟩ := mem_biUnion.mp hP
  obtain ⟨i, _, rfl⟩ := mem_image.mp hP
  obtain ⟨n, hn⟩ := hforms Q hQ
  exact ⟨n + 1, Nat.succ_pos _, hn.mul (isHomogeneous_X ℤ i)⟩

theorem positive_vanishing_iff {F : Type*} [Field F]
    (forms : Finset (MvPolynomial σ ℤ)) (a : σ → F) (ha : a ≠ 0) :
    (∀ P ∈ positiveForms forms, eval a (map (Int.castRingHom F) P) = 0) ↔
      ∀ P ∈ forms, eval a (map (Int.castRingHom F) P) = 0 := by
  constructor
  · intro h P hP
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hh := h (P * X i) (mem_biUnion.mpr ⟨P, hP, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
    simp only [map_mul, map_X, eval_X] at hh
    exact (mul_eq_zero.mp hh).resolve_right hi
  · intro h P hP
    obtain ⟨Q, hQ, hP⟩ := mem_biUnion.mp hP
    obtain ⟨i, _, rfl⟩ := mem_image.mp hP
    simp only [map_mul, map_X, eval_X, h Q hQ, zero_mul]

theorem positive_vanishes_at_zero {F : Type*} [CommRing F]
    (forms : Finset (MvPolynomial σ ℤ)) :
    ∀ P ∈ positiveForms forms, eval (0 : σ → F) (map (Int.castRingHom F) P) = 0 := by
  intro P hP
  obtain ⟨Q, _, hP⟩ := mem_biUnion.mp hP
  obtain ⟨i, _, rfl⟩ := mem_image.mp hP
  simp

theorem closed_field_equations
    (Y : Set (ProjectiveSpectrum (homogeneousSubmodule σ ℤ))) (hY : IsClosed Y) :
    ∃ forms : Finset (MvPolynomial σ ℤ),
      (∀ P ∈ forms, ∃ n : ℕ, 0 < n ∧ P.IsHomogeneous n) ∧
      (∀ (F : Type) [Field F] (a : σ → F) (ha : a ≠ 0),
        point a ha ∈ Y ↔ ∀ P ∈ forms, eval a (map (Int.castRingHom F) P) = 0) ∧
      ∀ (F : Type) [CommRing F],
        ∀ P ∈ forms, eval (0 : σ → F) (map (Int.castRingHom F) P) = 0 := by
  obtain ⟨forms, hhom, hYforms⟩ := ProjectiveIntegerClosedEquations.finite_equations Y hY
  refine ⟨positiveForms forms, positive_homogeneous forms hhom, ?_, ?_⟩
  · intro F _ a ha
    rw [positive_vanishing_iff forms a ha, hYforms]
    apply forall₂_congr
    intro P hP
    obtain ⟨n, hn⟩ := hhom P hP
    exact homogeneous_mem_iff a ha P hn
  · intro F _
    exact positive_vanishes_at_zero forms

end PaperP1.IntegerProjectiveEquationEvaluation
