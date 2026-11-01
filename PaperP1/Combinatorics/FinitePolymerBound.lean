module

public import PaperP1.Combinatorics.GraphStarPartition
public import PaperP1.Analysis.ExponentialPowerSum

/-! # A finite polymer bound from actual disjoint partitions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePolymerBound

open Finset

variable {V : Type*} [DecidableEq V]

def weight (w : V → ℝ) (S : Finset V) : ℝ := S.prod w

def generating (w : V → ℝ) (F : Finset (Finset V)) : ℝ := ∑ D ∈ F, weight w D

omit [DecidableEq V] in
theorem weight_nonneg (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (S : Finset V) : 0 ≤ weight w S :=
  prod_nonneg (fun v _ ↦ hw v)

theorem weight_eq_partition (w : V → ℝ) (D : Finset V) (P : Finset (Finset V))
    (hcover : P.biUnion id = D) (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id) :
    weight w D = ∏ S ∈ P, weight w S := by
  unfold weight
  calc
    _ = (P.biUnion id).prod w := congrArg (fun D : Finset V ↦ D.prod w) hcover.symm
    _ = _ := prod_biUnion hdisj

theorem generating_le_product (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F A : Finset (Finset V))
    (hpart : ∀ D ∈ F, ∃ P ⊆ A, P.biUnion id = D ∧ (↑P : Set (Finset V)).PairwiseDisjoint id) :
    generating w F ≤ ∏ S ∈ A, (1 + weight w S) := by
  classical
  let select (D : Finset V) : Finset (Finset V) := if h : D ∈ F then Classical.choose (hpart D h) else ∅
  have hs (D : Finset V) (hD : D ∈ F) : select D ⊆ A ∧ (select D).biUnion id = D ∧
      (↑(select D) : Set (Finset V)).PairwiseDisjoint id := by
    dsimp [select]
    rw [dite_eq_left hD]
    exact Classical.choose_spec (hpart D hD)
  have hinj : Set.InjOn select (↑F : Set (Finset V)) := by
    intro D hD E hE h
    have heq := congrArg (fun P : Finset (Finset V) ↦ P.biUnion id) h
    rw [(hs D hD).2.1, (hs E hE).2.1] at heq
    exact heq
  have hsub : F.image select ⊆ A.powerset := by
    intro P hP
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hP
    exact mem_powerset.mpr (hs D hD).1
  calc
    _ = ∑ P ∈ F.image select, ∏ S ∈ P, weight w S := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro D hD
      exact weight_eq_partition w D (select D) (hs D hD).2.1 (hs D hD).2.2
    _ ≤ ∑ P ∈ A.powerset, ∏ S ∈ P, weight w S :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ prod_nonneg (fun S _ ↦ weight_nonneg w hw S))
    _ = _ := (prod_one_add A).symm

theorem generating_le_exp (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F A : Finset (Finset V))
    (hpart : ∀ D ∈ F, ∃ P ⊆ A, P.biUnion id = D ∧ (↑P : Set (Finset V)).PairwiseDisjoint id) :
    generating w F ≤ Real.exp (∑ S ∈ A, weight w S) :=
  (generating_le_product w hw F A hpart).trans
    (Real.prod_one_add_le_exp_sum A (weight_nonneg w hw))

end PaperP1.FinitePolymerBound
