module

public import PaperP1.Analysis.TransposedNormalizedGraphPiece
public import PaperP1.Algebra.GraphControlPolynomials

/-! # Canonical actual dependent-coordinate derivatives in both graph orientations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BothGraphDerivativeFormulas

open MvPolynomial Set PlaneCoordinateSwap GraphControlPolynomials

theorem continuousOn_first (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : GraphTangentEvaluation.Trajectory P φ s) :
    ContinuousOn (fun t ↦ fun i ↦ φ i t) s := by
  apply continuousOn_pi.mpr
  intro i
  exact HasDerivAt.continuousOn (fun t ht ↦ hφ.2 t ht i)

theorem continuousOn_second (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) :
    ContinuousOn (fun t ↦ fun i ↦ φ i t) s := by
  apply continuousOn_pi.mpr
  intro i
  exact HasDerivAt.continuousOn (fun t ht ↦ hφ.2 t ht i)

theorem first (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hφ : GraphTangentEvaluation.Trajectory P φ s) (n : ℕ) :
    EqOn (iteratedDeriv (n + 1) (φ 1))
      (fun t ↦ eval (fun i ↦ φ i t) (orientedNumerator P 0 n) /
        (eval (fun i ↦ φ i t) (pderiv 1 P)) ^ (2 * n + 1)) s := by
  simpa [orientedNumerator] using
    IteratedGraphDerivative.iterated_evaluation P (X 1) φ s hs hφ n

theorem transpose_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) :
    GraphTangentEvaluation.Trajectory (polynomial P) (fun i t ↦ φ (index i) t) s := by
  have hA (t : ℝ) : eval (point (fun i ↦ φ i t)) (pderiv 1 (polynomial P)) =
      eval (fun i ↦ φ i t) (pderiv 0 P) := by
    simpa only [index_zero] using evaluation_partial P (fun i ↦ φ i t) 0
  have hB (t : ℝ) : eval (point (fun i ↦ φ i t)) (pderiv 0 (polynomial P)) =
      eval (fun i ↦ φ i t) (pderiv 1 P) := by
    simpa only [index_one] using evaluation_partial P (fun i ↦ φ i t) 1
  refine ⟨?_, ?_⟩
  · intro t ht
    change eval (point (fun i ↦ φ i t)) (pderiv 1 (polynomial P)) ≠ 0
    rw [hA]
    exact hφ.1 t ht
  · intro t ht i
    have hv : TransposedNormalizedGraphPiece.velocity P (fun j ↦ φ j t) (index i) =
        GraphTangentEvaluation.velocity (polynomial P) (point (fun j ↦ φ j t)) i := by
      fin_cases i
      · simp [TransposedNormalizedGraphPiece.velocity, GraphTangentEvaluation.velocity]
      · simp [TransposedNormalizedGraphPiece.velocity, GraphTangentEvaluation.velocity, hA, hB]
    exact (hφ.2 t ht (index i)).congr_deriv hv

theorem second (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s) (n : ℕ) :
    EqOn (iteratedDeriv (n + 1) (φ 0))
      (fun t ↦ eval (fun i ↦ φ i t) (orientedNumerator P 1 n) /
        (eval (fun i ↦ φ i t) (pderiv 0 P)) ^ (2 * n + 1)) s := by
  have hx := IteratedGraphDerivative.iterated_evaluation (polynomial P) (X 1)
    (fun i t ↦ φ (index i) t) s hs (transpose_trajectory P φ s hφ) n
  simp only [eval_X, index_one] at hx
  intro t ht
  simp only [orientedNumerator, show (1 : Fin 2) ≠ 0 by decide, ite_false, evaluation]
  have he := evaluation_partial P (fun i ↦ φ i t) 0
  rw [index_zero] at he
  rw [← he]
  exact hx ht

end PaperP1.BothGraphDerivativeFormulas
