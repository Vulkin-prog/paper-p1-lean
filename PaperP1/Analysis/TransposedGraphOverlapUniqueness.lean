module

public import PaperP1.Analysis.NormalizedGraphOverlapUniqueness
public import PaperP1.Analysis.BothGraphDerivativeFormulas

/-! # Actual overlap uniqueness in the second-coordinate graph orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransposedGraphOverlapUniqueness

open MvPolynomial Set PlaneCoordinateSwap


def firstPiece (P : MvPolynomial (Fin 2) ℝ) (q : TransposedNormalizedGraphPiece.Piece P) :
    LocalNormalizedGraphPiece.Piece (polynomial P) where
  left := q.left
  right := q.right
  ordered := q.ordered
  path := fun i t ↦ q.path (index i) t
  trajectory := BothGraphDerivativeFormulas.transpose_trajectory P q.path _ q.trajectory
  equation := by
    intro t ht
    change eval (point (fun i ↦ q.path i t)) (polynomial P) = 0
    rw [evaluation_polynomial_at_point]
    exact q.equation t ht
  first_coordinate := by
    intro t ht
    simpa only [index_zero] using q.second_coordinate t ht

theorem overlap_eq (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) :
    ∀ t ∈ Ioo q₁.left q₁.right, t ∈ Ioo q₂.left q₂.right →
      (fun i ↦ q₁.path i t) = (fun i ↦ q₂.path i t) := by
  have hinit : (fun i ↦ (firstPiece P q₁).path i t₀) = (fun i ↦ (firstPiece P q₂).path i t₀) := by
    funext i
    exact congrFun he (index i)
  intro t ht h't
  have hh := NormalizedGraphOverlapUniqueness.overlap_eq (polynomial P) (firstPiece P q₁) (firstPiece P q₂)
    t₀ ht₁ ht₂ hinit t ht h't
  funext i
  have hi := congrFun hh (index i)
  change q₁.path (index (index i)) t = q₂.path (index (index i)) t at hi
  simpa only [index_twice] using hi

end PaperP1.TransposedGraphOverlapUniqueness
