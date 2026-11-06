module

public import PaperP1.Algebra.P3HomogeneousMonomialWeights
public import Mathlib.Tactic.Linarith

/-! # The exact integer height-weight budget after removing multiples of the leading monomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardMonomialWeightBudget

open Finset P3HomogeneousCoefficientFamily P3StandardMonomialCount NormalizedP3MonomialHeight
open scoped Classical

theorem cardinality_add (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    Fintype.card (StandardIndex μ e) + (e - μ.degree + 3).choose 3 = (e + 3).choose 3 := by
  have hc : Fintype.card (Index (e - μ.degree)) ≤ Fintype.card (Index e) := by
    calc
      _ = Fintype.card {r : Index e // μ ≤ r.val} := Fintype.card_congr (multipleEquiv μ e he)
      _ ≤ _ := Fintype.card_subtype_le _
  rw [index_card, index_card] at hc
  rw [cardinality μ e he]
  exact Nat.sub_add_cancel hc

theorem multiple_free_sum (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    (∑ r : {r : Index e // μ ≤ r.val}, freeDegree r.val.val) =
      Fintype.card (Index (e - μ.degree)) * freeDegree μ + ∑ r : Index (e - μ.degree), freeDegree r.val := by
  classical
  calc
    _ = ∑ r : Index (e - μ.degree), freeDegree (μ + r.val) :=
      ((multipleEquiv μ e he).sum_comp (fun r ↦ freeDegree r.val.val)).symm
    _ = _ := by
      simp only [P3HomogeneousMonomialWeights.freeDegree_add, sum_add_distrib, sum_const,
        card_univ, Nat.nsmul_eq_mul]

theorem free_sum_split (μ : Fin 4 →₀ ℕ) (e : ℕ) :
    (∑ r : StandardIndex μ e, freeDegree r.val.val) +
      (∑ r : {r : Index e // μ ≤ r.val}, freeDegree r.val.val) = ∑ r : Index e, freeDegree r.val := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun r : Index e ↦ μ ≤ r.val) (fun r ↦ freeDegree r.val)
  exact (add_comm _ _).trans h

theorem scaled_free_budget (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) (hμ : μ 3 = 0) :
    4 * (∑ r : StandardIndex μ e, freeDegree r.val.val) +
      (4 * μ.degree + 3 * (e - μ.degree)) * (e - μ.degree + 3).choose 3 =
        3 * e * (e + 3).choose 3 := by
  have hμfree : freeDegree μ = μ.degree := by
    have hh := NormalizedP3MonomialHeight.degree_split μ
    simpa only [hμ, add_zero] using hh
  have hsplit := free_sum_split μ e
  have hmultiple := multiple_free_sum μ e he
  rw [hμfree, index_card] at hmultiple
  have hfull := P3HomogeneousMonomialWeights.free_budget e
  have hsmall := P3HomogeneousMonomialWeights.free_budget (e - μ.degree)
  rw [index_card] at hfull hsmall
  nlinarith only [hsplit, hmultiple, hfull, hsmall]

end PaperP1.P3StandardMonomialWeightBudget
