module

public import PaperP1.Algebra.PolynomialGradientDegree
public import PaperP1.Algebra.MvPlaneBezout

/-! # Exact real singular populations and a finite exceptional set

One actual nonzero partial of smaller degree supplies the Bezout bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneSingularPoints

open MvPolynomial Set Finset PolynomialGradientDegree

def points (P : MvPolynomial (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  {z | eval z P = 0 ∧ ∀ i, eval z (pderiv i P) = 0}

theorem population_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hdegree : 0 < P.totalDegree) (S : Finset (Fin 2 → ℝ)) (hS : ∀ z ∈ S, z ∈ points P) :
    S.card ≤ P.totalDegree * (P.totalDegree - 1) := by
  obtain ⟨i, _hi, hnot⟩ := exists_partial_not_dvd P hdegree
  exact (MvPlaneBezout.common_points_card P (pderiv i P) hP hnot S
    (fun z hz ↦ ⟨(hS z hz).1, (hS z hz).2 i⟩)).trans
      (Nat.mul_le_mul_left _ (pderiv_degree_le_sub_one P i))

theorem exists_finset (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P) (hdegree : 0 < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ), (∀ z, z ∈ E ↔ z ∈ points P) ∧
      E.card ≤ P.totalDegree * (P.totalDegree - 1) := by
  classical
  have hf : (points P).Finite := by
    by_contra hbad
    have hInf : (points P).Infinite := hbad
    obtain ⟨S, hS, hcard⟩ := hInf.exists_subset_card_eq (P.totalDegree * (P.totalDegree - 1) + 1)
    have hc := population_card P hP hdegree S (fun z hz ↦ hS hz)
    omega
  exact ⟨hf.toFinset, fun z ↦ hf.mem_toFinset,
    population_card P hP hdegree hf.toFinset (fun z hz ↦ hf.mem_toFinset.mp hz)⟩

theorem gradient_nonzero_of_not_mem (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hnot : z ∉ points P) : ∃ i : Fin 2, eval z (pderiv i P) ≠ 0 := by
  by_contra hbad
  push Not at hbad
  exact hnot ⟨hzero, hbad⟩

end PaperP1.PlaneSingularPoints
