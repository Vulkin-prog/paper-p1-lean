module

public import PaperP1.Analysis.TransposedNormalizedGraphPiece
public import PaperP1.Algebra.PlaneSingularPoints

/-! # Both actual normalized graph orientations at every nonsingular point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularNormalizedCharts

open MvPolynomial Set PlaneCoordinateSwap
open scoped ContDiff

theorem exists_at_nonsingular (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hgradient : ∃ j, eval z (pderiv j P) ≠ 0) :
    ∃ i : Fin 2, ∃ a b : ℝ, ∃ φ : Fin 2 → ℝ → ℝ,
      z i ∈ Ioo a b ∧ (fun j ↦ φ j (z i)) = z ∧
      (∀ t ∈ Ioo a b, φ i t = t) ∧ (∀ j, ContDiffOn ℝ ∞ (φ j) (Ioo a b)) ∧
      (∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) P = 0) ∧
      (∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) (pderiv (index i) P) ≠ 0) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, ∀ n : ℕ, 1 ≤ n →
        ∃ N : MvPolynomial (Fin 2) ℝ,
          N.totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * n ∧
          EqOn (iteratedDeriv n (fun t ↦ eval (fun j ↦ φ j t) Q))
            (fun t ↦ eval (fun j ↦ φ j t) N /
              (eval (fun j ↦ φ j t) (pderiv (index i) P)) ^ (2 * n - 1)) (Ioo a b) := by
  obtain ⟨j, hj⟩ := hgradient
  fin_cases j
  · obtain ⟨r, hmem, hpoint, hsmooth, hder⟩ :=
      TransposedNormalizedGraphPiece.exists_smooth_piece_with_derivatives P z hzero hj
    refine ⟨1, r.left, r.right, r.path, hmem, hpoint, r.second_coordinate, hsmooth, r.equation, ?_, ?_⟩
    · simpa only [index_one] using r.trajectory.1
    · simpa only [index_one] using hder
  · obtain ⟨r, hmem, hpoint, hsmooth, hder⟩ :=
      LocalNormalizedGraphPiece.exists_smooth_piece_with_derivatives P z hzero hj
    refine ⟨0, r.left, r.right, r.path, hmem, hpoint, r.first_coordinate, hsmooth, r.equation, ?_, ?_⟩
    · simpa only [index_zero] using r.trajectory.1
    · simpa only [index_zero] using hder

theorem exists_off_singular (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hnot : z ∉ PlaneSingularPoints.points P) :
    ∃ i : Fin 2, ∃ a b : ℝ, ∃ φ : Fin 2 → ℝ → ℝ,
      z i ∈ Ioo a b ∧ (fun j ↦ φ j (z i)) = z ∧
      (∀ t ∈ Ioo a b, φ i t = t) ∧ (∀ j, ContDiffOn ℝ ∞ (φ j) (Ioo a b)) ∧
      (∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) P = 0) ∧
      (∀ t ∈ Ioo a b, eval (fun j ↦ φ j t) (pderiv (index i) P) ≠ 0) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, ∀ n : ℕ, 1 ≤ n →
        ∃ N : MvPolynomial (Fin 2) ℝ,
          N.totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * n ∧
          EqOn (iteratedDeriv n (fun t ↦ eval (fun j ↦ φ j t) Q))
            (fun t ↦ eval (fun j ↦ φ j t) N /
              (eval (fun j ↦ φ j t) (pderiv (index i) P)) ^ (2 * n - 1)) (Ioo a b) :=
  exists_at_nonsingular P z hzero (PlaneSingularPoints.gradient_nonzero_of_not_mem P z hzero hnot)

end PaperP1.RegularNormalizedCharts
