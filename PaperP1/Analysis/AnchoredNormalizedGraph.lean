module

public import PaperP1.Analysis.NormalizedGraphGluing
public import PaperP1.Analysis.NormalizedGraphImageNeighborhood

/-! # Actual anchored graph charts and attachment through a shared curve point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredNormalizedGraph

open MvPolynomial Set LocalNormalizedGraphPiece


def pointImage {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) : Set (Fin 2 → ℝ) :=
  (fun t ↦ fun i ↦ q.path i t) '' Ioo q.left q.right

structure Anchored (P : MvPolynomial (Fin 2) ℝ) (C : Set (Fin 2 → ℝ)) (anchor : Fin 2 → ℝ) where
  chart : Piece P
  anchor_mem : anchor 0 ∈ Ioo chart.left chart.right
  anchor_eq : (fun i ↦ chart.path i (anchor 0)) = anchor
  image_subset : pointImage chart ⊆ C

theorem parameter_of_point {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (w : Fin 2 → ℝ)
    (hw : w ∈ pointImage q) :
    w 0 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (w 0)) = w := by
  obtain ⟨t, ht, he⟩ := hw
  have hc : w 0 = t := by rw [← he]; exact q.first_coordinate t ht
  rw [hc]
  exact ⟨ht, he⟩

theorem anchor_in_image {P : MvPolynomial (Fin 2) ℝ} {C : Set (Fin 2 → ℝ)} {anchor : Fin 2 → ℝ}
    (A : Anchored P C anchor) : anchor ∈ pointImage A.chart :=
  ⟨anchor 0, A.anchor_mem, A.anchor_eq⟩

theorem attach {P : MvPolynomial (Fin 2) ℝ} {C : Set (Fin 2 → ℝ)} {anchor : Fin 2 → ℝ}
    (A : Anchored P C anchor) (q : Piece P) (hq : pointImage q ⊆ C)
    (v : Fin 2 → ℝ) (hvA : v ∈ pointImage A.chart) (hvq : v ∈ pointImage q) :
    ∃ B : Anchored P C anchor, pointImage A.chart ⊆ pointImage B.chart ∧ pointImage q ⊆ pointImage B.chart := by
  obtain ⟨hv₁, he₁⟩ := parameter_of_point A.chart v hvA
  obtain ⟨hv₂, he₂⟩ := parameter_of_point q v hvq
  let g := NormalizedGraphGluing.glue A.chart q (v 0) hv₁ hv₂ (he₁.trans he₂.symm)
  have hI : pointImage g = pointImage A.chart ∪ pointImage q :=
    NormalizedGraphGluing.image_union A.chart q (v 0) hv₁ hv₂ (he₁.trans he₂.symm)
  let B : Anchored P C anchor := {
    chart := g
    anchor_mem := by
      change anchor 0 ∈ Ioo (min A.chart.left q.left) (max A.chart.right q.right)
      rw [← NormalizedGraphGluing.domain_union A.chart q (v 0) hv₁ hv₂]
      exact Or.inl A.anchor_mem
    anchor_eq := by
      have he : (fun i ↦ g.path i (anchor 0)) = (fun i ↦ A.chart.path i (anchor 0)) :=
        funext (fun i ↦ NormalizedGraphGluing.path_eq_left A.chart q i A.anchor_mem)
      exact he.trans A.anchor_eq
    image_subset := by
      rw [hI]
      exact union_subset A.image_subset hq }
  refine ⟨B, ?_, ?_⟩
  · change pointImage A.chart ⊆ pointImage g
    rw [hI]
    exact subset_union_left
  · change pointImage q ⊆ pointImage g
    rw [hI]
    exact subset_union_right

end PaperP1.AnchoredNormalizedGraph
