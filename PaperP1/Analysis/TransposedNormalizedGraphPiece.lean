module

public import PaperP1.Algebra.PlaneCoordinateSwap
public import PaperP1.Analysis.LocalNormalizedGraphPiece

/-! # Constructed smooth graphs with the second coordinate as parameter

All statements concern the original polynomial and original point coordinates.
The exact transposition transports the internally constructed first orientation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransposedNormalizedGraphPiece

open MvPolynomial Set PlaneCoordinateSwap
open scoped ContDiff

def velocity (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i = 1 then 1 else -eval z (pderiv 1 P) / eval z (pderiv 0 P)

def Trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, eval (fun i ↦ φ i t) (pderiv 0 P) ≠ 0) ∧
    ∀ t ∈ s, ∀ i, HasDerivAt (φ i) (velocity P (fun j ↦ φ j t) i) t

structure Piece (P : MvPolynomial (Fin 2) ℝ) where
  left : ℝ
  right : ℝ
  ordered : left < right
  path : Fin 2 → ℝ → ℝ
  trajectory : Trajectory P path (Ioo left right)
  equation : ∀ t ∈ Ioo left right, eval (fun i ↦ path i t) P = 0
  second_coordinate : ∀ t ∈ Ioo left right, path 1 t = t

theorem transpose_trajectory (P : MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hφ : GraphTangentEvaluation.Trajectory (polynomial P) φ s) :
    Trajectory P (fun i t ↦ φ (index i) t) s := by
  have hA (t : ℝ) : eval (fun i ↦ φ i t) (pderiv 1 (polynomial P)) =
      eval (point (fun i ↦ φ i t)) (pderiv 0 P) := by
    simpa only [index_zero] using evaluation_pderiv P (fun i ↦ φ i t) 0
  have hB (t : ℝ) : eval (fun i ↦ φ i t) (pderiv 0 (polynomial P)) =
      eval (point (fun i ↦ φ i t)) (pderiv 1 P) := by
    simpa only [index_one] using evaluation_pderiv P (fun i ↦ φ i t) 1
  refine ⟨?_, ?_⟩
  · intro t ht
    change eval (point (fun i ↦ φ i t)) (pderiv 0 P) ≠ 0
    rw [← hA]
    exact hφ.1 t ht
  · intro t ht i
    have hv : GraphTangentEvaluation.velocity (polynomial P) (fun j ↦ φ j t) (index i) =
        velocity P (point (fun j ↦ φ j t)) i := by
      fin_cases i
      · simp [GraphTangentEvaluation.velocity, velocity, hA, hB]
      · simp [GraphTangentEvaluation.velocity, velocity]
    exact (hφ.2 t ht (index i)).congr_deriv hv

def transposePiece (P : MvPolynomial (Fin 2) ℝ)
    (r : LocalNormalizedGraphPiece.Piece (polynomial P)) : Piece P where
  left := r.left
  right := r.right
  ordered := r.ordered
  path := fun i t ↦ r.path (index i) t
  trajectory := transpose_trajectory P r.path _ r.trajectory
  equation := by
    intro t ht
    change eval (point (fun i ↦ r.path i t)) P = 0
    rw [← evaluation]
    exact r.equation t ht
  second_coordinate := by
    intro t ht
    simpa only [index_one] using r.first_coordinate t ht

theorem initial_point (P : MvPolynomial (Fin 2) ℝ)
    (r : LocalNormalizedGraphPiece.Piece (polynomial P)) (z : Fin 2 → ℝ)
    (hpoint : (fun i ↦ r.path i (z 1)) = point z) :
    (fun i ↦ (transposePiece P r).path i (z 1)) = z := by
  funext i
  simpa only [transposePiece, point, index_twice] using congrFun hpoint (index i)

theorem exists_piece (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 0 P) ≠ 0) :
    ∃ r : Piece P, z 1 ∈ Ioo r.left r.right ∧ (fun i ↦ r.path i (z 1)) = z := by
  have hz : eval (point z) (polynomial P) = 0 := by
    rw [evaluation_polynomial_at_point]
    exact hzero
  have hden : eval (point z) (pderiv 1 (polynomial P)) ≠ 0 := by
    have he := evaluation_partial P z 0
    rw [index_zero] at he
    rw [he]
    exact hA
  obtain ⟨r, hmem, hpoint⟩ := LocalNormalizedGraphPiece.exists_piece (polynomial P) (point z) hz hden
  have ht : point z 0 = z 1 := by simp only [point, index_zero]
  rw [ht] at hmem hpoint
  exact ⟨transposePiece P r, hmem, initial_point P r z hpoint⟩

theorem exists_smooth_piece_with_derivatives (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hA : eval z (pderiv 0 P) ≠ 0) :
    ∃ r : Piece P, z 1 ∈ Ioo r.left r.right ∧ (fun i ↦ r.path i (z 1)) = z ∧
      (∀ i, ContDiffOn ℝ ∞ (r.path i) (Ioo r.left r.right)) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, ∀ j : ℕ, 1 ≤ j →
        ∃ N : MvPolynomial (Fin 2) ℝ,
          N.totalDegree ≤ Q.totalDegree + 2 * P.totalDegree * j ∧
          EqOn (iteratedDeriv j (fun t ↦ eval (fun i ↦ r.path i t) Q))
            (fun t ↦ eval (fun i ↦ r.path i t) N /
              (eval (fun i ↦ r.path i t) (pderiv 0 P)) ^ (2 * j - 1))
            (Ioo r.left r.right) := by
  have hz : eval (point z) (polynomial P) = 0 := by
    rw [evaluation_polynomial_at_point]
    exact hzero
  have hden : eval (point z) (pderiv 1 (polynomial P)) ≠ 0 := by
    have he := evaluation_partial P z 0
    rw [index_zero] at he
    rw [he]
    exact hA
  obtain ⟨r, hmem, hpoint, hsmooth, hder⟩ :=
    LocalNormalizedGraphPiece.exists_smooth_piece_with_derivatives (polynomial P) (point z) hz hden
  have ht : point z 0 = z 1 := by simp only [point, index_zero]
  rw [ht] at hmem hpoint
  let q := transposePiece P r
  refine ⟨q, hmem, initial_point P r z hpoint, (fun i ↦ hsmooth (index i)), ?_⟩
  intro Q j hj
  obtain ⟨N, hdegree, hformula⟩ := hder (polynomial Q) j hj
  refine ⟨polynomial N, ?_, ?_⟩
  · simpa only [degree] using hdegree
  · have hfun : (fun t ↦ eval (fun i ↦ q.path i t) Q) =
        (fun t ↦ eval (fun i ↦ r.path i t) (polynomial Q)) := by
      funext t
      exact (evaluation Q (fun i ↦ r.path i t)).symm
    rw [hfun]
    intro t hmemt
    change iteratedDeriv j (fun t ↦ eval (fun i ↦ r.path i t) (polynomial Q)) t =
      eval (point (fun i ↦ r.path i t)) (polynomial N) /
        (eval (point (fun i ↦ r.path i t)) (pderiv 0 P)) ^ (2 * j - 1)
    rw [evaluation_polynomial_at_point]
    have he := evaluation_pderiv P (fun i ↦ r.path i t) 0
    rw [index_zero] at he
    rw [← he]
    exact hformula hmemt

end PaperP1.TransposedNormalizedGraphPiece
