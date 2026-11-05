module

public import PaperP1.Analysis.NormalizedGraphGluing
public import PaperP1.Analysis.TransposedGraphOverlapUniqueness

/-! # Constructed gluing and exact image union in the second graph orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransposedGraphGluing

open MvPolynomial Set PlaneCoordinateSwap TransposedGraphOverlapUniqueness


def glue (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) : TransposedNormalizedGraphPiece.Piece P :=
  TransposedNormalizedGraphPiece.transposePiece P
    (NormalizedGraphGluing.glue (firstPiece P q₁) (firstPiece P q₂) t₀ ht₁ ht₂
      (funext (fun i ↦ congrFun he (index i))))

theorem path_eq_left (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) (i : Fin 2) :
    EqOn ((glue P q₁ q₂ t₀ ht₁ ht₂ he).path i) (q₁.path i) (Ioo q₁.left q₁.right) := by
  intro t ht
  change NormalizedGraphGluing.path (firstPiece P q₁) (firstPiece P q₂) (index i) t = q₁.path i t
  have hh := NormalizedGraphGluing.path_eq_left (firstPiece P q₁) (firstPiece P q₂) (index i) ht
  have hcoord : (firstPiece P q₁).path (index i) t = q₁.path i t := by
    change q₁.path (index (index i)) t = q₁.path i t
    rw [index_twice]
  exact hh.trans hcoord

theorem path_eq_right (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) (i : Fin 2) :
    EqOn ((glue P q₁ q₂ t₀ ht₁ ht₂ he).path i) (q₂.path i) (Ioo q₂.left q₂.right) := by
  intro t ht
  change NormalizedGraphGluing.path (firstPiece P q₁) (firstPiece P q₂) (index i) t = q₂.path i t
  have hinit : (fun j ↦ (firstPiece P q₁).path j t₀) = (fun j ↦ (firstPiece P q₂).path j t₀) :=
    funext (fun j ↦ congrFun he (index j))
  have hh := NormalizedGraphGluing.path_eq_right (firstPiece P q₁) (firstPiece P q₂) t₀ ht₁ ht₂ hinit (index i) ht
  have hcoord : (firstPiece P q₂).path (index i) t = q₂.path i t := by
    change q₂.path (index (index i)) t = q₂.path i t
    rw [index_twice]
  exact hh.trans hcoord

theorem image_union (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) :
    let q := glue P q₁ q₂ t₀ ht₁ ht₂ he
    (fun t ↦ fun i ↦ q.path i t) '' Ioo q.left q.right =
      ((fun t ↦ fun i ↦ q₁.path i t) '' Ioo q₁.left q₁.right) ∪
        ((fun t ↦ fun i ↦ q₂.path i t) '' Ioo q₂.left q₂.right) := by
  have hdom : Ioo q₁.left q₁.right ∪ Ioo q₂.left q₂.right = Ioo (min q₁.left q₂.left) (max q₁.right q₂.right) :=
    Ioo_union_Ioo' (ht₂.1.trans ht₁.2) (ht₁.1.trans ht₂.2)
  ext w
  constructor
  · rintro ⟨t, ht, hw⟩
    change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right) at ht
    rw [← hdom] at ht
    rcases ht with hh | hh
    · exact Or.inl ⟨t, hh, (funext (fun i ↦ path_eq_left P q₁ q₂ t₀ ht₁ ht₂ he i hh)).symm.trans hw⟩
    · exact Or.inr ⟨t, hh, (funext (fun i ↦ path_eq_right P q₁ q₂ t₀ ht₁ ht₂ he i hh)).symm.trans hw⟩
  · intro hw
    rcases hw with ⟨t, ht, hw⟩ | ⟨t, ht, hw⟩
    · refine ⟨t, ?_, (funext (fun i ↦ path_eq_left P q₁ q₂ t₀ ht₁ ht₂ he i ht)).trans hw⟩
      change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)
      rw [← hdom]
      exact Or.inl ht
    · refine ⟨t, ?_, (funext (fun i ↦ path_eq_right P q₁ q₂ t₀ ht₁ ht₂ he i ht)).trans hw⟩
      change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)
      rw [← hdom]
      exact Or.inr ht

end PaperP1.TransposedGraphGluing
