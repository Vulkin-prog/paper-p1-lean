module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Actual finite homogeneous generators of a Noetherian multivariate polynomial ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteHomogeneousIdealBasis

open MvPolynomial Finset
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R]

def components (S : Finset (MvPolynomial σ R)) : Finset (MvPolynomial σ R) :=
  S.biUnion (fun P ↦ (range (P.totalDegree + 1)).image (fun n ↦ homogeneousComponent n P))

theorem components_homogeneous (S : Finset (MvPolynomial σ R)) (P : MvPolynomial σ R)
    (hP : P ∈ components S) : ∃ n : ℕ, P.IsHomogeneous n := by
  obtain ⟨Q, _hQ, hh⟩ := mem_biUnion.mp hP
  obtain ⟨n, _hn, rfl⟩ := mem_image.mp hh
  exact ⟨n, homogeneousComponent_isHomogeneous n Q⟩

theorem components_mem (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (S : Finset (MvPolynomial σ R)) (hS : Ideal.span (S : Set (MvPolynomial σ R)) = I)
    (P : MvPolynomial σ R) (hP : P ∈ components S) : P ∈ I := by
  obtain ⟨Q, hQ, hh⟩ := mem_biUnion.mp hP
  obtain ⟨n, _hn, rfl⟩ := mem_image.mp hh
  have hQI : Q ∈ I := hS ▸ Ideal.subset_span hQ
  exact homogeneousComponent_mem_of_mem hI hQI n

theorem span_components (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (S : Finset (MvPolynomial σ R)) (hS : Ideal.span (S : Set (MvPolynomial σ R)) = I) :
    Ideal.span (components S : Set (MvPolynomial σ R)) = I := by
  apply le_antisymm
  · exact Ideal.span_le.mpr (fun P hP ↦ components_mem I hI S hS P hP)
  · rw [← hS]
    apply Ideal.span_le.mpr
    intro P hP
    rw [← sum_homogeneousComponent P]
    apply Ideal.sum_mem
    intro n hn
    exact Ideal.subset_span (mem_biUnion.mpr ⟨P, hP, mem_image.mpr ⟨n, hn, rfl⟩⟩)

theorem exists_generators [IsNoetherianRing (MvPolynomial σ R)]
    (I : Ideal (MvPolynomial σ R)) (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    ∃ forms : Finset (MvPolynomial σ R),
      (∀ P ∈ forms, ∃ n : ℕ, P.IsHomogeneous n) ∧ Ideal.span (forms : Set (MvPolynomial σ R)) = I := by
  obtain ⟨S, hS⟩ := (show I.FG from IsNoetherian.noetherian I)
  exact ⟨components S, components_homogeneous S, span_components I hI S hS⟩

end PaperP1.FiniteHomogeneousIdealBasis
