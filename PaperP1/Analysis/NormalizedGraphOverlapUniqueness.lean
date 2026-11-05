module

public import PaperP1.Analysis.RegularCurveProjectionUniqueness
public import PaperP1.Analysis.LocalNormalizedGraphPiece

/-! # Actual normalized graph charts agreeing at one point agree on their overlap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGraphOverlapUniqueness

open MvPolynomial Set LocalNormalizedGraphPiece RegularCurveProjectionUniqueness
open scoped ContDiff


def lift {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (a b : ℝ)
    (hsub : Ioo a b ⊆ Ioo q.left q.right) : Ioo a b → RegularX P := fun t ↦
  ⟨(fun i ↦ q.path i t.val), q.equation t.val (hsub t.property), q.trajectory.1 t.val (hsub t.property)⟩

theorem lift_continuous {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (a b : ℝ)
    (hsub : Ioo a b ⊆ Ioo q.left q.right) : Continuous (lift q a b hsub) := by
  have hsmooth := GraphTangentSmooth.contDiffOn_trajectory P q.path (Ioo q.left q.right) isOpen_Ioo q.trajectory
  have hc : Continuous (fun t : Ioo a b ↦ fun i ↦ q.path i t.val) := by
    apply continuous_pi
    intro i
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hsmooth i).continuousOn.continuousAt (isOpen_Ioo.mem_nhds (hsub t.property))).comp
      continuous_subtype_val.continuousAt
  exact hc.subtype_mk _

theorem lift_projection {P : MvPolynomial (Fin 2) ℝ} (q : Piece P) (a b : ℝ)
    (hsub : Ioo a b ⊆ Ioo q.left q.right) (t : Ioo a b) :
    projection (lift q a b hsub t) = t.val := q.first_coordinate t.val (hsub t.property)

theorem overlap_eq (P : MvPolynomial (Fin 2) ℝ) (q₁ q₂ : Piece P)
    (t₀ : ℝ) (ht₁ : t₀ ∈ Ioo q₁.left q₁.right) (ht₂ : t₀ ∈ Ioo q₂.left q₂.right)
    (he : (fun i ↦ q₁.path i t₀) = (fun i ↦ q₂.path i t₀)) :
    ∀ t ∈ Ioo q₁.left q₁.right, t ∈ Ioo q₂.left q₂.right →
      (fun i ↦ q₁.path i t) = (fun i ↦ q₂.path i t) := by
  let a := max q₁.left q₂.left
  let b := min q₁.right q₂.right
  have hsub₁ : Ioo a b ⊆ Ioo q₁.left q₁.right :=
    fun _ ht ↦ ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hsub₂ : Ioo a b ⊆ Ioo q₂.left q₂.right :=
    fun _ ht ↦ ⟨(le_max_right _ _).trans_lt ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have ht₀ : t₀ ∈ Ioo a b := ⟨max_lt ht₁.1 ht₂.1, lt_min ht₁.2 ht₂.2⟩
  let : PreconnectedSpace (Ioo a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hproj : projection ∘ lift q₁ a b hsub₁ = projection ∘ lift q₂ a b hsub₂ := by
    funext t
    exact (lift_projection q₁ a b hsub₁ t).trans (lift_projection q₂ a b hsub₂ t).symm
  have hinit : lift q₁ a b hsub₁ ⟨t₀, ht₀⟩ = lift q₂ a b hsub₂ ⟨t₀, ht₀⟩ := Subtype.ext he
  have hsame := (projection_separated P).eq_of_comp_eq (projection_locally_injective P)
    (lift_continuous q₁ a b hsub₁) (lift_continuous q₂ a b hsub₂) hproj ⟨t₀, ht₀⟩ hinit
  intro t ht h't
  have hts : t ∈ Ioo a b := ⟨max_lt ht.1 h't.1, lt_min ht.2 h't.2⟩
  exact congrArg Subtype.val (congrFun hsame ⟨t, hts⟩)

end PaperP1.NormalizedGraphOverlapUniqueness
