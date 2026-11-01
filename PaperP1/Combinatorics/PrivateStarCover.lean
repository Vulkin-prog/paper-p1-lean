module

public import PaperP1.Combinatorics.MinimalFiniteCover
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Private leaves turn a minimal edge cover into disjoint stars -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateStarCover

open Finset

variable {V : Type*} [DecidableEq V]

def IsBlock (G : SimpleGraph V) (marks S : Finset V) : Prop :=
  (∃ v ∈ marks, S = {v}) ∨
    ∃ c ∈ S, (S.erase c).Nonempty ∧ ∀ v ∈ S.erase c, G.Adj c v

structure PrivateFamily (G : SimpleGraph V) (marks : Finset V) where
  edges : Finset (Finset V)
  leaf : edges → V
  center : edges → V
  edge_eq : ∀ e, e.val = {center e, leaf e}
  private_leaf : ∀ e f, leaf e ∈ f.val → f = e
  leaf_adj : ∀ e, center e ≠ leaf e → G.Adj (center e) (leaf e)
  center_marked : ∀ e, center e = leaf e → center e ∈ marks

variable {G : SimpleGraph V} {marks : Finset V}

def roots (F : PrivateFamily G marks) : Finset V := univ.image F.center

def block (F : PrivateFamily G marks) (c : V) : Finset V :=
  (univ.filter (fun e : F.edges ↦ F.center e = c)).biUnion (fun e ↦ e.val)

def blocks (F : PrivateFamily G marks) : Finset (Finset V) := (roots F).image (block F)

theorem mem_roots (F : PrivateFamily G marks) (c : V) : c ∈ roots F ↔ ∃ e, F.center e = c := by
  simp only [roots, mem_image, mem_univ, true_and]

theorem mem_block (F : PrivateFamily G marks) (c v : V) :
    v ∈ block F c ↔ ∃ e : F.edges, F.center e = c ∧ v ∈ e.val := by
  simp only [block, mem_biUnion, mem_filter, mem_univ, true_and]

theorem center_mem_block (F : PrivateFamily G marks) (c : V) (hc : c ∈ roots F) : c ∈ block F c := by
  obtain ⟨e, he⟩ := (mem_roots F c).mp hc
  apply (mem_block F c c).mpr
  exact ⟨e, he, by rw [F.edge_eq e, he]; exact mem_insert_self _ _⟩

theorem common_vertex_centers_eq (F : PrivateFamily G marks) (c d v : V)
    (hvc : v ∈ block F c) (hvd : v ∈ block F d) : c = d := by
  obtain ⟨e, he, hve⟩ := (mem_block F c v).mp hvc
  obtain ⟨f, hf, hvf⟩ := (mem_block F d v).mp hvd
  have hve' := hve
  have hvf' := hvf
  rw [F.edge_eq e] at hve'
  rw [F.edge_eq f] at hvf'
  rcases mem_insert.mp hve' with hvc' | hvl
  · rcases mem_insert.mp hvf' with hvd' | hvl'
    · exact he.symm.trans (hvc'.symm.trans (hvd'.trans hf))
    · have hleaf : F.leaf f ∈ e.val := (mem_singleton.mp hvl') ▸ hve
      have hef := F.private_leaf f e hleaf
      rw [hef] at he
      exact he.symm.trans hf
  · have hleaf : F.leaf e ∈ f.val := (mem_singleton.mp hvl) ▸ hvf
    have hfe := F.private_leaf e f hleaf
    rw [hfe] at hf
    exact he.symm.trans hf

theorem roots_pairwise_disjoint (F : PrivateFamily G marks) :
    (↑(roots F) : Set V).PairwiseDisjoint (block F) := by
  intro c _ d _ hcd
  apply disjoint_left.mpr
  intro v hvc hvd
  exact hcd (common_vertex_centers_eq F c d v hvc hvd)

theorem blocks_pairwise_disjoint (F : PrivateFamily G marks) :
    (↑(blocks F) : Set (Finset V)).PairwiseDisjoint id := by
  intro A hA B hB hAB
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hA
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hB
  apply roots_pairwise_disjoint F hc hd
  exact fun h ↦ hAB (congrArg (block F) h)

theorem blocks_cover (F : PrivateFamily G marks) : (blocks F).biUnion id = F.edges.biUnion id := by
  ext v
  constructor
  · intro hv
    obtain ⟨S, hS, hvS⟩ := mem_biUnion.mp hv
    obtain ⟨c, _, rfl⟩ := mem_image.mp hS
    obtain ⟨e, _, hve⟩ := (mem_block F c v).mp hvS
    exact mem_biUnion.mpr ⟨e.val, e.property, hve⟩
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    let a : F.edges := ⟨e, he⟩
    have hc : F.center a ∈ roots F := (mem_roots F _).mpr ⟨a, rfl⟩
    exact mem_biUnion.mpr ⟨block F (F.center a), mem_image.mpr ⟨_, hc, rfl⟩,
      (mem_block F _ v).mpr ⟨a, rfl, hve⟩⟩

theorem block_isBlock (F : PrivateFamily G marks) (c : V) (hc : c ∈ roots F) :
    IsBlock G marks (block F c) := by
  have hcblock := center_mem_block F c hc
  by_cases hsingle : block F c = {c}
  · left
    obtain ⟨e, he⟩ := (mem_roots F c).mp hc
    have hleaf : F.leaf e ∈ block F c :=
      (mem_block F c _).mpr ⟨e, he, by rw [F.edge_eq e]; exact mem_insert_of_mem (mem_singleton_self _)⟩
    rw [hsingle, mem_singleton] at hleaf
    have hsame : F.center e = F.leaf e := he.trans hleaf.symm
    exact ⟨c, he ▸ F.center_marked e hsame, hsingle⟩
  · right
    refine ⟨c, hcblock, ?_, ?_⟩
    · by_contra hnot
      have hempty : (block F c).erase c = ∅ := not_nonempty_iff_eq_empty.mp hnot
      have h := insert_erase hcblock
      rw [hempty] at h
      exact hsingle h.symm
    · intro v hv
      obtain ⟨hvc, hvblock⟩ := mem_erase.mp hv
      obtain ⟨e, he, hve⟩ := (mem_block F c v).mp hvblock
      rw [F.edge_eq e] at hve
      rcases mem_insert.mp hve with hve | hve
      · exact False.elim (hvc (hve.trans he))
      · have hleaf : v = F.leaf e := mem_singleton.mp hve
        have hne : F.center e ≠ F.leaf e := by
          intro h
          exact hvc (hleaf.trans (h.symm.trans he))
        simpa only [he, ← hleaf] using F.leaf_adj e hne

theorem blocks_isBlock (F : PrivateFamily G marks) : ∀ S ∈ blocks F, IsBlock G marks S := by
  intro S hS
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hS
  exact block_isBlock F c hc

end PaperP1.PrivateStarCover
