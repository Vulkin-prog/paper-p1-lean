module

public import PaperP1.Combinatorics.PrivateStarCover

/-! # Actual admissible vertex sets have disjoint star partitions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphStarPartition

open Finset PaperP1.PrivateStarCover

variable {V : Type*} [DecidableEq V]

def Admissible (G : SimpleGraph V) (marks D : Finset V) : Prop :=
  ∀ v ∈ D, v ∈ marks ∨ ∃ w ∈ D, G.Adj v w

def AllowedAtom (G : SimpleGraph V) (marks e : Finset V) : Prop :=
  (∃ v ∈ marks, e = {v}) ∨ ∃ u v, G.Adj u v ∧ e = {u, v}

def atoms (G : SimpleGraph V) (marks D : Finset V) : Finset (Finset V) := by
  classical
  exact D.powerset.filter (AllowedAtom G marks)

theorem admissible_iff_isolated_marked (G : SimpleGraph V) (marks D : Finset V) :
    Admissible G marks D ↔ ∀ v ∈ D, (∀ w ∈ D, ¬G.Adj v w) → v ∈ marks := by
  classical
  constructor
  · intro h v hv hiso
    rcases h v hv with hm | ⟨w, hw, hadj⟩
    · exact hm
    · exact False.elim (hiso w hw hadj)
  · intro h v hv
    by_cases hm : v ∈ marks
    · exact Or.inl hm
    · right
      by_contra hn
      apply hm
      apply h v hv
      intro w hw hadj
      exact hn ⟨w, hw, hadj⟩

theorem mem_atoms (G : SimpleGraph V) (marks D e : Finset V) :
    e ∈ atoms G marks D ↔ e ⊆ D ∧ AllowedAtom G marks e := by
  classical
  simp only [atoms, mem_filter, mem_powerset]

theorem atoms_cover (G : SimpleGraph V) (marks D : Finset V) (hD : Admissible G marks D) :
    (atoms G marks D).biUnion id = D := by
  classical
  apply subset_antisymm
  · intro v hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
    exact ((mem_atoms G marks D e).mp he).1 hv
  · intro v hv
    rcases hD v hv with hm | ⟨w, hw, hadj⟩
    · have he : {v} ∈ atoms G marks D := (mem_atoms G marks D _).mpr
        ⟨singleton_subset_iff.mpr hv, Or.inl ⟨v, hm, rfl⟩⟩
      exact mem_biUnion.mpr ⟨{v}, he, mem_singleton_self _⟩
    · have he : {v, w} ∈ atoms G marks D := (mem_atoms G marks D _).mpr
        ⟨insert_subset hv (singleton_subset_iff.mpr hw), Or.inr ⟨v, w, hadj, rfl⟩⟩
      exact mem_biUnion.mpr ⟨{v, w}, he, mem_insert_self _ _⟩

theorem atom_center_exists (G : SimpleGraph V) (marks e : Finset V) (l : V)
    (hl : l ∈ e) (he : AllowedAtom G marks e) :
    ∃ c, e = {c, l} ∧ (c = l → c ∈ marks) ∧ (c ≠ l → G.Adj c l) := by
  rcases he with ⟨v, hm, hev⟩ | ⟨u, v, hadj, hev⟩
  · have hlv : l = v := by simpa only [hev, mem_singleton] using hl
    refine ⟨v, ?_, fun _ ↦ hm, ?_⟩
    · simp only [hev, hlv, insert_eq_of_mem (mem_singleton_self v)]
    · exact fun h ↦ False.elim (h hlv.symm)
  · have hl' : l = u ∨ l = v := by simpa only [hev, mem_insert, mem_singleton] using hl
    rcases hl' with hlu | hlv
    · refine ⟨v, ?_, ?_, ?_⟩
      · rw [hev, hlu, pair_comm]
      · intro h
        exact False.elim (hadj.ne (hlu.symm.trans h.symm))
      · intro _
        simpa only [hlu] using hadj.symm
    · refine ⟨u, ?_, ?_, ?_⟩
      · rw [hev, hlv]
      · intro h
        exact False.elim (hadj.ne (h.trans hlv))
      · intro _
        simpa only [hlv] using hadj

theorem exists_private_family (G : SimpleGraph V) (marks D : Finset V) (hD : Admissible G marks D) :
    ∃ F : PrivateFamily G marks, F.edges.biUnion id = D := by
  classical
  obtain ⟨E, hEA, hED, hprivate⟩ := PaperP1.MinimalFiniteCover.exists_private_cover
    (atoms G marks D) D (atoms_cover G marks D hD)
  let leaf : E → V := fun e ↦ Classical.choose (hprivate e.val e.property)
  have hleaf (e : E) : leaf e ∈ e.val := (Classical.choose_spec (hprivate e.val e.property)).1
  have hpriv (e f : E) (h : leaf e ∈ f.val) : f = e :=
    Subtype.ext ((Classical.choose_spec (hprivate e.val e.property)).2 f.val f.property h)
  have hc (e : E) : ∃ c, e.val = {c, leaf e} ∧
      (c = leaf e → c ∈ marks) ∧ (c ≠ leaf e → G.Adj c (leaf e)) :=
    atom_center_exists G marks e.val (leaf e) (hleaf e) ((mem_atoms G marks D e.val).mp (hEA e.property)).2
  let center : E → V := fun e ↦ Classical.choose (hc e)
  let F : PrivateFamily G marks := {
    edges := E
    leaf := leaf
    center := center
    edge_eq := fun e ↦ (Classical.choose_spec (hc e)).1
    private_leaf := hpriv
    leaf_adj := fun e ↦ (Classical.choose_spec (hc e)).2.2
    center_marked := fun e ↦ (Classical.choose_spec (hc e)).2.1 }
  exact ⟨F, hED⟩

theorem exists_partition (G : SimpleGraph V) (marks D : Finset V) (hD : Admissible G marks D) :
    ∃ P : Finset (Finset V), P.biUnion id = D ∧
      (↑P : Set (Finset V)).PairwiseDisjoint id ∧ ∀ S ∈ P, IsBlock G marks S := by
  obtain ⟨F, hFD⟩ := exists_private_family G marks D hD
  exact ⟨blocks F, (blocks_cover F).trans hFD, blocks_pairwise_disjoint F, blocks_isBlock F⟩

end PaperP1.GraphStarPartition
