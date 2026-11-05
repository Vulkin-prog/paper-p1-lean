module

public import PaperP1.Analysis.NormalizedGraphOverlapUniqueness

/-! # Constructed gluing of actual overlapping normalized graph charts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGraphGluing

open MvPolynomial Set Filter LocalNormalizedGraphPiece
open scoped Topology


def path {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P) (i : Fin 2) (t : ℝ) : ℝ :=
  if t ∈ Ioo q₁.left q₁.right then q₁.path i t else q₂.path i t

theorem path_eq_left {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P) (i : Fin 2) :
    EqOn (path q₁ q₂ i) (q₁.path i) (Ioo q₁.left q₁.right) := fun _ ht ↦ ite_eq_left ht

theorem path_eq_right {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) (i : Fin 2) :
    EqOn (path q₁ q₂ i) (q₂.path i) (Ioo q₂.left q₂.right) := by
  intro t ht
  by_cases hfirst : t ∈ Ioo q₁.left q₁.right
  · rw [path, ite_eq_left hfirst]
    exact congrFun (NormalizedGraphOverlapUniqueness.overlap_eq P q₁ q₂ t₀ ht₁ ht₂ he t hfirst ht) i
  · exact ite_eq_right hfirst

theorem domain_union {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P) (t₀ : ℝ)
    (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right) :
    Ioo q₁.left q₁.right ∪ Ioo q₂.left q₂.right = Ioo (min q₁.left q₂.left) (max q₁.right q₂.right) :=
  Ioo_union_Ioo' (ht₂.1.trans ht₁.2) (ht₁.1.trans ht₂.2)

theorem trajectory_of_eqOn {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (φ : Fin 2 → ℝ → ℝ)
    (heq : ∀ i, EqOn (φ i) (q.path i) (Ioo q.left q.right)) :
    GraphTangentEvaluation.Trajectory P φ (Ioo q.left q.right) := by
  have he (t : ℝ) (ht : t ∈ Ioo q.left q.right) : (fun i ↦ φ i t) = (fun i ↦ q.path i t) :=
    funext (fun i ↦ heq i ht)
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [he t ht]
    exact q.trajectory.1 t ht
  · intro t ht i
    have hlocal : φ i =ᶠ[𝓝 t] q.path i := (heq i).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
    have hd := (q.trajectory.2 t ht i).congr_of_eventuallyEq hlocal
    rw [← he t ht] at hd
    exact hd

theorem trajectory {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) :
    GraphTangentEvaluation.Trajectory P (path q₁ q₂) (Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)) := by
  have hleft := trajectory_of_eqOn q₁ (path q₁ q₂) (path_eq_left q₁ q₂)
  have hright := trajectory_of_eqOn q₂ (path q₁ q₂) (path_eq_right q₁ q₂ t₀ ht₁ ht₂ he)
  have hcases (t : ℝ) (ht : t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)) :
      t ∈ Ioo q₁.left q₁.right ∨ t ∈ Ioo q₂.left q₂.right := by
    rw [← domain_union q₁ q₂ t₀ ht₁ ht₂] at ht
    exact ht
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases hcases t ht with hh | hh
    · exact hleft.1 t hh
    · exact hright.1 t hh
  · intro t ht i
    rcases hcases t ht with hh | hh
    · exact hleft.2 t hh i
    · exact hright.2 t hh i

theorem equation {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀))
    (t : ℝ) (ht : t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)) :
    eval (fun i ↦ path q₁ q₂ i t) P = 0 := by
  rw [← domain_union q₁ q₂ t₀ ht₁ ht₂] at ht
  rcases ht with hh | hh
  · have heq := funext (fun i ↦ path_eq_left q₁ q₂ i hh)
    rw [heq]
    exact q₁.equation t hh
  · have heq := funext (fun i ↦ path_eq_right q₁ q₂ t₀ ht₁ ht₂ he i hh)
    rw [heq]
    exact q₂.equation t hh

theorem first_coordinate {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀))
    (t : ℝ) (ht : t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)) : path q₁ q₂ 0 t = t := by
  rw [← domain_union q₁ q₂ t₀ ht₁ ht₂] at ht
  rcases ht with hh | hh
  · exact (path_eq_left q₁ q₂ 0 hh).trans (q₁.first_coordinate t hh)
  · exact (path_eq_right q₁ q₂ t₀ ht₁ ht₂ he 0 hh).trans (q₂.first_coordinate t hh)

def glue {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) : Piece P where
  left := min q₁.left q₂.left
  right := max q₁.right q₂.right
  ordered := ((min_le_left _ _).trans_lt ht₁.1).trans (ht₁.2.trans_le (le_max_left _ _))
  path := path q₁ q₂
  trajectory := trajectory q₁ q₂ t₀ ht₁ ht₂ he
  equation := equation q₁ q₂ t₀ ht₁ ht₂ he
  first_coordinate := first_coordinate q₁ q₂ t₀ ht₁ ht₂ he

theorem image_union {P : MvPolynomial (Fin 2) ℝ} (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) :
    let q := glue q₁ q₂ t₀ ht₁ ht₂ he
    (fun t ↦ fun i ↦ q.path i t) '' Ioo q.left q.right =
      ((fun t ↦ fun i ↦ q₁.path i t) '' Ioo q₁.left q₁.right) ∪
        ((fun t ↦ fun i ↦ q₂.path i t) '' Ioo q₂.left q₂.right) := by
  ext w
  constructor
  · rintro ⟨t, ht, hw⟩
    change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right) at ht
    rw [← domain_union q₁ q₂ t₀ ht₁ ht₂] at ht
    rcases ht with hh | hh
    · apply Or.inl
      exact ⟨t, hh, (funext (fun i ↦ path_eq_left q₁ q₂ i hh)).symm.trans hw⟩
    · apply Or.inr
      exact ⟨t, hh, (funext (fun i ↦ path_eq_right q₁ q₂ t₀ ht₁ ht₂ he i hh)).symm.trans hw⟩
  · intro hw
    rcases hw with ⟨t, ht, hw⟩ | ⟨t, ht, hw⟩
    · refine ⟨t, ?_, (funext (fun i ↦ path_eq_left q₁ q₂ i ht)).trans hw⟩
      change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)
      rw [← domain_union q₁ q₂ t₀ ht₁ ht₂]
      exact Or.inl ht
    · refine ⟨t, ?_, (funext (fun i ↦ path_eq_right q₁ q₂ t₀ ht₁ ht₂ he i ht)).trans hw⟩
      change t ∈ Ioo (min q₁.left q₂.left) (max q₁.right q₂.right)
      rw [← domain_union q₁ q₂ t₀ ht₁ ht₂]
      exact Or.inr ht

end PaperP1.NormalizedGraphGluing
