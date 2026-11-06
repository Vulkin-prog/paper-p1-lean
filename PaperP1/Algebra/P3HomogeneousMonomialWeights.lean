module

public import PaperP1.Algebra.P3StandardMonomialCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact total height weights of the actual homogeneous four-coordinate monomial population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HomogeneousMonomialWeights

open Finset P3HomogeneousCoefficientFamily NormalizedP3MonomialHeight
open scoped Classical

theorem permuted_degree (π : Fin 4 ≃ Fin 4) (r : Fin 4 →₀ ℕ) :
    (Finsupp.domCongr π r).degree = r.degree := by
  change (Finsupp.equivMapDomain π r).degree = _
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

def permute (d : ℕ) (π : Fin 4 ≃ Fin 4) : Index d ≃ Index d where
  toFun r := ⟨Finsupp.domCongr π r.val, (permuted_degree π r.val).trans r.property⟩
  invFun r := ⟨Finsupp.domCongr π.symm r.val, (permuted_degree π.symm r.val).trans r.property⟩
  left_inv r := Subtype.ext ((Finsupp.domCongr π).symm_apply_apply r.val)
  right_inv r := Subtype.ext ((Finsupp.domCongr π).apply_symm_apply r.val)

theorem coordinate_sum_eq (d : ℕ) (i j : Fin 4) :
    (∑ r : Index d, r.val i) = ∑ r : Index d, r.val j := by
  classical
  have he := (permute d (Equiv.swap i j)).sum_comp (fun r : Index d ↦ r.val j)
  have hp (r : Index d) : (permute d (Equiv.swap i j) r).val j = r.val i := by
    change (Finsupp.equivMapDomain (Equiv.swap i j) r.val) j = _
    simp only [Finsupp.equivMapDomain_apply, Equiv.symm_swap, Equiv.swap_apply_right]
  simpa only [hp] using he

theorem coordinate_budget (d : ℕ) :
    4 * (∑ r : Index d, r.val 0) = d * Fintype.card (Index d) := by
  have hd (r : Index d) : (∑ i : Fin 4, r.val i) = d := by
    rw [← Finsupp.degree_eq_sum]
    exact r.property
  have he : (∑ r : Index d, ∑ i : Fin 4, r.val i) = d * Fintype.card (Index d) := by
    simp only [hd, sum_const, card_univ]
    change Fintype.card (Index d) * d = d * Fintype.card (Index d)
    exact Nat.mul_comm _ _
  rw [sum_comm] at he
  have hcoords (i : Fin 4) : (∑ r : Index d, r.val i) = ∑ r : Index d, r.val 0 :=
    coordinate_sum_eq d i 0
  simpa only [hcoords, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using he

theorem free_sum (d : ℕ) :
    (∑ r : Index d, freeDegree r.val) = 3 * ∑ r : Index d, r.val 0 := by
  unfold freeDegree
  rw [sum_comm]
  have hcoords (i : Fin 3) : (∑ r : Index d, r.val i.castSucc) = ∑ r : Index d, r.val 0 :=
    coordinate_sum_eq d i.castSucc 0
  simp only [hcoords, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

theorem free_budget (d : ℕ) :
    4 * (∑ r : Index d, freeDegree r.val) = 3 * d * Fintype.card (Index d) := by
  rw [free_sum]
  calc
    4 * (3 * ∑ r : Index d, r.val 0) = 3 * (4 * ∑ r : Index d, r.val 0) := by ring
    _ = 3 * (d * Fintype.card (Index d)) := by rw [coordinate_budget]
    _ = _ := by ring

theorem freeDegree_add (μ ν : Fin 4 →₀ ℕ) : freeDegree (μ + ν) = freeDegree μ + freeDegree ν := by
  simp only [freeDegree, Finsupp.add_apply, sum_add_distrib]

end PaperP1.P3HomogeneousMonomialWeights
