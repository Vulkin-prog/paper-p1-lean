module

public import PaperP1.Combinatorics.FinitePolymerBound

/-! # Exact finite star weights and a heterogeneous graph generating bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphStarWeights

open Finset PaperP1.PrivateStarCover PaperP1.GraphStarPartition PaperP1.FinitePolymerBound

theorem sum_union_le_nonneg {W : Type*} [DecidableEq W] (s t : Finset W)
    (f : W → ℝ) (hf : ∀ v, 0 ≤ f v) : (∑ v ∈ s ∪ t, f v) ≤ (∑ v ∈ s, f v) + ∑ v ∈ t, f v := by
  have h := (sum_union_inter : (∑ v ∈ s ∪ t, f v) + ∑ v ∈ s ∩ t, f v =
    (∑ v ∈ s, f v) + ∑ v ∈ t, f v)
  have hpos : 0 ≤ ∑ v ∈ s ∩ t, f v := sum_nonneg (fun v _ ↦ hf v)
  linarith

theorem sum_biUnion_le_nonneg {I W : Type*} [DecidableEq W] (s : Finset I)
    (A : I → Finset W) (f : W → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ v ∈ s.biUnion A, f v) ≤ ∑ i ∈ s, ∑ v ∈ A i, f v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    exact (sum_union_le_nonneg (A i) (s.biUnion A) f hf).trans (add_le_add (le_refl _) ih)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def starLeaves (c : V) : Finset (Finset V) := (G.neighborFinset c).powerset.erase ∅

def starBlocks (c : V) : Finset (Finset V) := (starLeaves G c).image (insert c)

def allBlocks (marks : Finset V) : Finset (Finset V) := marks.image singleton ∪ univ.biUnion (starBlocks G)

def families (marks : Finset V) : Finset (Finset V) := by
  classical
  exact univ.powerset.filter (Admissible G marks)

theorem mem_starLeaves (c : V) (L : Finset V) :
    L ∈ starLeaves G c ↔ L.Nonempty ∧ L ⊆ G.neighborFinset c := by
  simp only [starLeaves, mem_erase, mem_powerset, nonempty_iff_ne_empty]

omit [DecidableEq V] in
theorem center_not_mem_leaves (c : V) (L : Finset V) (hL : L ⊆ G.neighborFinset c) : c ∉ L := by
  intro hc
  exact G.irrefl ((G.mem_neighborFinset c c).mp (hL hc))

theorem isBlock_mem_allBlocks (marks S : Finset V) (hS : IsBlock G marks S) : S ∈ allBlocks G marks := by
  rcases hS with ⟨v, hv, rfl⟩ | ⟨c, hc, hnonempty, hadj⟩
  · exact mem_union_left _ (mem_image.mpr ⟨v, hv, rfl⟩)
  · apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨c, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨S.erase c, (mem_starLeaves G c _).mpr ⟨hnonempty, ?_⟩, insert_erase hc⟩
    intro v hv
    exact (G.mem_neighborFinset c v).mpr (hadj v hv)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_families (marks D : Finset V) : D ∈ families G marks ↔ Admissible G marks D := by
  classical
  simp only [families, mem_filter, mem_powerset, subset_univ, true_and]

theorem star_block_weight (w : V → ℝ) (c : V) (L : Finset V) (hL : L ⊆ G.neighborFinset c) :
    weight w (insert c L) = w c * weight w L := by
  exact prod_insert (center_not_mem_leaves G c L hL)

theorem star_leaves_weight (w : V → ℝ) (c : V) :
    (∑ L ∈ starLeaves G c, weight w L) = (∏ v ∈ G.neighborFinset c, (1 + w v)) - 1 := by
  have he := sum_erase_add (G.neighborFinset c).powerset (weight w)
    (empty_mem_powerset (G.neighborFinset c))
  have hprod : (∑ L ∈ (G.neighborFinset c).powerset, weight w L) =
      ∏ v ∈ G.neighborFinset c, (1 + w v) := (prod_one_add _).symm
  change (∑ L ∈ starLeaves G c, weight w L) + weight w ∅ = _ at he
  rw [show weight w ∅ = 1 from prod_empty, hprod] at he
  linarith

theorem star_blocks_weight_le (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (c : V) :
    (∑ S ∈ starBlocks G c, weight w S) ≤ w c * ((∏ v ∈ G.neighborFinset c, (1 + w v)) - 1) := by
  calc
    _ ≤ ∑ L ∈ starLeaves G c, weight w (insert c L) :=
      sum_image_le_of_nonneg (fun S _ ↦ weight_nonneg w hw S)
    _ = ∑ L ∈ starLeaves G c, w c * weight w L := by
      apply sum_congr rfl
      intro L hL
      exact star_block_weight G w c L ((mem_starLeaves G c L).mp hL).2
    _ = w c * ∑ L ∈ starLeaves G c, weight w L := by rw [mul_sum]
    _ = _ := by rw [star_leaves_weight]

theorem all_blocks_weight_le (marks : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    (∑ S ∈ allBlocks G marks, weight w S) ≤ (∑ v ∈ marks, w v) +
      ∑ c, w c * ((∏ v ∈ G.neighborFinset c, (1 + w v)) - 1) := by
  have hm : (∑ S ∈ marks.image singleton, weight w S) ≤ ∑ v ∈ marks, w v := by
    have h := sum_image_le_of_nonneg (s := marks) (g := singleton) (f := weight w)
      (fun S _ ↦ weight_nonneg w hw S)
    simpa only [weight, prod_singleton] using h
  have hs : (∑ S ∈ univ.biUnion (starBlocks G), weight w S) ≤
      ∑ c, w c * ((∏ v ∈ G.neighborFinset c, (1 + w v)) - 1) := by
    calc
      _ ≤ ∑ c, ∑ S ∈ starBlocks G c, weight w S :=
        sum_biUnion_le_nonneg univ (starBlocks G) (weight w) (weight_nonneg w hw)
      _ ≤ _ := sum_le_sum (fun c _ ↦ star_blocks_weight_le G w hw c)
  exact (sum_union_le_nonneg _ _ (weight w) (weight_nonneg w hw)).trans (add_le_add hm hs)

theorem heterogeneous_generating_bound (marks : Finset V) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    generating w (families G marks) ≤ Real.exp ((∑ v ∈ marks, w v) +
      ∑ c, w c * ((∏ v ∈ G.neighborFinset c, (1 + w v)) - 1)) := by
  have hpart : ∀ D ∈ families G marks, ∃ P ⊆ allBlocks G marks,
      P.biUnion id = D ∧ (↑P : Set (Finset V)).PairwiseDisjoint id := by
    intro D hD
    obtain ⟨P, hcover, hdisj, hblock⟩ := exists_partition G marks D ((mem_families G marks D).mp hD)
    exact ⟨P, (fun S hS ↦ isBlock_mem_allBlocks G marks S (hblock S hS)), hcover, hdisj⟩
  exact (generating_le_exp w hw (families G marks) (allBlocks G marks) hpart).trans
    (Real.exp_le_exp.mpr (all_blocks_weight_le G marks w hw))

end PaperP1.GraphStarWeights
