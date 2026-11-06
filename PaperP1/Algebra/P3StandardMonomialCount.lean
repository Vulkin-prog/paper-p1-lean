module

public import PaperP1.Algebra.P3HomogeneousCoefficientFamily
public import PaperP1.Algebra.P3HeightLeadingMonomial
public import Mathlib.Data.Fintype.Card

/-! # The literal standard degree-e monomial population modulo one actual leading monomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardMonomialCount

open P3HomogeneousCoefficientFamily
open scoped Classical

abbrev StandardIndex (μ : Fin 4 →₀ ℕ) (e : ℕ) := {r : Index e // ¬ μ ≤ r.val}

def multipleEquiv (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    Index (e - μ.degree) ≃ {r : Index e // μ ≤ r.val} where
  toFun r := ⟨⟨μ + r.val, by rw [map_add, r.property]; omega⟩, le_self_add⟩
  invFun r := ⟨r.val.val - μ, by
    have hsum := congrArg Finsupp.degree (add_tsub_cancel_of_le r.property)
    simp only [map_add, r.val.property] at hsum
    omega⟩
  left_inv r := by
    apply Subtype.ext
    exact add_tsub_cancel_left μ r.val
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_tsub_cancel_of_le r.property

theorem cardinality (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    Fintype.card (StandardIndex μ e) = (e + 3).choose 3 - (e - μ.degree + 3).choose 3 := by
  classical
  have hc : Fintype.card {r : Index e // μ ≤ r.val} = Fintype.card (Index (e - μ.degree)) :=
    (Fintype.card_congr (multipleEquiv μ e he)).symm
  change Fintype.card {r : Index e // ¬ μ ≤ r.val} = _
  rw [Fintype.card_subtype_compl, hc, index_card, index_card]

theorem exponent_injective (μ : Fin 4 →₀ ℕ) (e : ℕ) :
    Function.Injective (fun r : StandardIndex μ e ↦ r.val.val) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem exponent_degree (μ : Fin 4 →₀ ℕ) (e : ℕ) (r : StandardIndex μ e) : r.val.val.degree = e :=
  r.val.property

theorem exponent_standard (μ : Fin 4 →₀ ℕ) (e : ℕ) (r : StandardIndex μ e) : ¬ μ ≤ r.val.val :=
  r.property

end PaperP1.P3StandardMonomialCount
