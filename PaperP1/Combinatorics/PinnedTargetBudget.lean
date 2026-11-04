module

public import PaperP1.Combinatorics.PinnedTargetRestriction
public import PaperP1.Combinatorics.TargetComponentBudget

/-! # The exact target-size budget for projected pinned graph solutions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PinnedTargetBudget

open Finset PaperP1.Arithmetic PaperP1.PinnedTargetRestriction

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def support (G : SimpleGraph V) (c : G.ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset

theorem mem_support (G : SimpleGraph V) (c : G.ConnectedComponent) (v : V) :
    v ∈ support G c ↔ G.connectedComponentMk v = c := by
  classical
  simp only [support, Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem support_injective (G : SimpleGraph V) : Function.Injective (support G) := by
  intro c d he
  have hc : c.out ∈ support G c := (mem_support G c c.out).mpr c.out_eq
  have hd : c.out ∈ support G d := he ▸ hc
  exact c.out_eq.symm.trans ((mem_support G d c.out).mp hd)

def family (G : SimpleGraph V) (pins T : Finset V) : Finset (Finset V) :=
  (components G pins T).image (support G)

theorem family_card (G : SimpleGraph V) (pins T : Finset V) :
    (family G pins T).card = (components G pins T).card :=
  card_image_of_injective _ (support_injective G)

theorem family_disjoint (G : SimpleGraph V) (pins T : Finset V) :
    (family G pins T : Set (Finset V)).Pairwise Disjoint := by
  intro A hA B hB hne
  obtain ⟨c, _hc, rfl⟩ := mem_image.mp hA
  obtain ⟨d, _hd, rfl⟩ := mem_image.mp hB
  apply disjoint_left.mpr
  intro v hvc hvd
  have he : c = d := ((mem_support G c v).mp hvc).symm.trans ((mem_support G d v).mp hvd)
  exact hne (congrArg (support G) he)

theorem meeting_eq_family (G : SimpleGraph V) (pins T : Finset V) :
    TargetComponentBudget.meeting (family G pins T) T = family G pins T := by
  classical
  apply filter_eq_self.mpr
  intro A hA
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hA
  obtain ⟨_hfree, v, hvT, he⟩ := (mem_components G pins T c).mp hc
  exact ⟨v, mem_inter.mpr ⟨(mem_support G c v).mpr he, hvT⟩⟩

theorem component_budget (G : SimpleGraph V) (pins T : Finset V) :
    2 * (components G pins T).card ≤ T.card + (TargetComponentBudget.singleton (family G pins T) T).card := by
  have hh := TargetComponentBudget.singleton_budget (family G pins T) T (family_disjoint G pins T)
  rw [meeting_eq_family, family_card] at hh
  exact hh

theorem projected_budget {ι : Type*} [Fintype ι] (G : SimpleGraph V) (pins T : Finset V) (e : ι → V)
    (hcover : ∀ i, e i ∈ T ∪ pins) :
    2 * Module.finrank F₂ (LinearMap.range (restrictionOn G pins e)) ≤
      T.card + (TargetComponentBudget.singleton (family G pins T) T).card := by
  have hrank := finrank_restrictionOn_le_of_pins G pins T e hcover
  have hbudget := component_budget G pins T
  omega

end PaperP1.PinnedTargetBudget
