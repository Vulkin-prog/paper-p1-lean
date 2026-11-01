module

public import PaperP1.Arithmetic.LocalRelationBlocks
public import PaperP1.Model.RunSeparation
public import PaperP1.Model.LocalRelationRows

/-! # The predecessor endpoint and deterministic Bernoulli support of a local block -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlockGeometry

open Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.Arithmetic
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability PaperP1.RunSeparation

theorem predecessor_mem_iff {x L : ℕ} (hx : 0 < x) (S : Finset ℕ) (hS : S.Nonempty)
    (hwin : S ⊆ window x L) : x - 1 ∈ S ↔ x = first S + 1 := by
  have hlo := (mem_Ico.mp (hwin (first_mem hS))).1
  constructor
  · intro h
    have hi := first_le hS h
    omega
  · intro h
    have he : x - 1 = first S := by omega
    rw [he]
    exact first_mem hS

theorem block_distance_lt {N L : ℕ} {S : Finset ℕ} (hS : Relation S)
    {x y : ℕ} (hx : x ∈ block N L S) (hy : y ∈ block N L S) : y < x + L := by
  have hxwin := ((mem_block N L S x).mp hx).2
  have hywin := ((mem_block N L S y).mp hy).2
  have hlast := (mem_Ico.mp (hxwin (last_mem hS.1))).2
  have hfirst := (mem_Ico.mp (hywin (first_mem hS.1))).1
  have hlt := relation_first_lt_last hS
  omega

theorem count_le_one {Ω : Type*} {N L : ℕ} {S : Finset ℕ} (hS : Relation S)
    (J : ℕ → Ω → Bool) (ω : Ω)
    (hsep : ∀ x ∈ block N L S, ∀ y ∈ block N L S, x < y → J x ω = true → J y ω = true → x + L ≤ y) :
    indicatorCount (block N L S) J ω ≤ 1 := by
  classical
  rw [← card_activeSites]
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx, hxactive⟩ := mem_filter.mp hx
  obtain ⟨hy, hyactive⟩ := mem_filter.mp hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h := hsep x hx y hy hlt hxactive hyactive
    have hdist := block_distance_lt hS hx hy
    omega
  · have h := hsep y hy x hx hlt hyactive hxactive
    have hdist := block_distance_lt hS hy hx
    omega

theorem infiniteCount_le_one {N L : ℕ} {S : Finset ℕ} (hS : Relation S)
    (ω : Model.InfiniteRademacher.InfiniteSample) : infiniteStartCount (block N L S) L ω ≤ 1 := by
  apply count_le_one hS (fun x ↦ infiniteStartIndicator x L) ω
  intro x _ y _ hxy hx hy
  exact infiniteStartIndicator_separated ω hx hy hxy

theorem finiteCount_le_one {M N L : ℕ} {S : Finset ℕ} (hS : Relation S) (σ : SampleSpace M) :
    indicatorCount (block N L S) (fun x ↦ startIndicator x L) σ ≤ 1 := by
  apply count_le_one hS (fun x ↦ startIndicator x L) σ
  intro x _ y _ hxy hx hy
  have hxevent : StartEvent (valueBit σ) x L := by simpa only [startIndicator, decide_eq_true_eq] using hx
  have hyevent : StartEvent (valueBit σ) y L := by simpa only [startIndicator, decide_eq_true_eq] using hy
  exact startEvent_separated _ hxevent hyevent hxy

theorem block_marginal {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂
      (WindowRelationCode.windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) {x : ℕ} (hx : x ∈ block N L S) :
    infiniteMarginal x L = if x = first S + 1 then 0 else 2 * (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨hxbox, hxwin⟩ := (mem_block N L S x).mp hx
  have hxpos : 0 < x := by have h := (mem_Ico.mp hxbox).1; omega
  have hrel := ((mem_relations N L S).mp hS).1
  rw [PaperP1.LocalRelationRows.one_relation_marginal hxpos hL (hrank x hxbox) S hxwin hrel]
  simp only [predecessor_mem_iff hxpos S hrel.1 hxwin]

end PaperP1.LocalBlockGeometry
