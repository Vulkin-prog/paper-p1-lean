module

public import PaperP1.Algebra.GraphControlPolynomials
public import PaperP1.Algebra.PolynomialAuxiliaryExceptions
public import PaperP1.Algebra.PlaneSingularPoints

/-! # Genuine finite derivative, slope and boundary exceptions

The actual control family has a quadratic degree and order budget. Singular
points are already contained in this locus; no extra singular bound is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphControlExceptions

open MvPolynomial Set GraphControlPolynomials PolynomialGradientDegree

def points (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) : Set (Fin 2 → ℝ) :=
  PolynomialAuxiliaryExceptions.points P (family P r)

theorem population_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, z ∈ points P r) :
    S.card ≤ 30 * P.totalDegree ^ 2 * (r + 1) ^ 2 :=
  (PolynomialAuxiliaryExceptions.population_card P hP (family P r) S hS).trans (bezout_budget P hD r)

theorem exists_finset (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) :
    ∃ E : Finset (Fin 2 → ℝ), (∀ z, z ∈ E ↔ z ∈ points P r) ∧
      E.card ≤ 30 * P.totalDegree ^ 2 * (r + 1) ^ 2 := by
  obtain ⟨E, hE, hc⟩ := PolynomialAuxiliaryExceptions.exists_finset P hP (family P r)
  exact ⟨E, hE, hc.trans (bezout_budget P hD r)⟩

theorem singular_mem (P : MvPolynomial (Fin 2) ℝ) (hD : 0 < P.totalDegree)
    (r : ℕ) (z : Fin 2 → ℝ) (hz : z ∈ PlaneSingularPoints.points P) : z ∈ points P r := by
  obtain ⟨i, _hi, hnot⟩ := exists_partial_not_dvd P hD
  refine ⟨hz.1, ?_⟩
  fin_cases i
  · exact ⟨Sum.inl 0, hnot, hz.2 0⟩
  · exact ⟨Sum.inl 1, hnot, hz.2 1⟩

theorem gradient_nonzero (P : MvPolynomial (Fin 2) ℝ) (hD : 0 < P.totalDegree)
    (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0) (hnot : z ∉ points P r) :
    ∃ i : Fin 2, eval z (pderiv i P) ≠ 0 := by
  apply PlaneSingularPoints.gradient_nonzero_of_not_mem P z hzero
  exact fun hz ↦ hnot (singular_mem P hD r z hz)

theorem divisible_or_nonzero (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hnot : z ∉ points P r) (i : Fin 10 ⊕ (Fin 2 × Fin r)) :
    P ∣ family P r i ∨ eval z (family P r i) ≠ 0 :=
  PolynomialAuxiliaryExceptions.divisible_or_nonzero P (family P r) z hzero hnot i

theorem restriction_zero_or_nowhere_zero (P : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (S : Set (Fin 2 → ℝ)) (hS : ∀ z ∈ S, eval z P = 0 ∧ z ∉ points P r)
    (i : Fin 10 ⊕ (Fin 2 × Fin r)) :
    (∀ z ∈ S, eval z (family P r i) = 0) ∨ (∀ z ∈ S, eval z (family P r i) ≠ 0) :=
  PolynomialAuxiliaryExceptions.restriction_zero_or_nowhere_zero P (family P r) S hS i

end PaperP1.GraphControlExceptions
