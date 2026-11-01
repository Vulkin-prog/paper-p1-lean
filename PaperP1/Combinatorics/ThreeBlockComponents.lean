module

public import PaperP1.Combinatorics.ColoredPrimeConstraints
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Free components meeting all three blocks and the exact remaining rank cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeBlockComponents

open Finset PaperP1.Arithmetic PaperP1.LocalDefectBound PaperP1.CoverGraphResolution
  PaperP1.ComponentSelection PaperP1.PinnedGraphResolution PaperP1.ColoredPrimeConstraints

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance threeBlockComponentTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance threeBlockDecidableAdj (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _
local instance threeBlockComponentDecidableEq (G : SimpleGraph V) : DecidableEq G.ConnectedComponent := Classical.decEq _

def Full (G : SimpleGraph V) (color : V → Fin 3) (c : G.ConnectedComponent) : Prop :=
  ∀ k : Fin 3, ∃ v ∈ c.supp, color v = k

def Missing (G : SimpleGraph V) (color : V → Fin 3) (k : Fin 3) (c : G.ConnectedComponent) : Prop :=
  ∀ v ∈ c.supp, color v ≠ k

def fullComponents (G : SimpleGraph V) (pins : Finset V) (color : V → Fin 3) : Finset G.ConnectedComponent := by
  classical
  exact univ.filter (fun c ↦ ¬ComponentPinned G pins c ∧ Full G color c)

def missingComponents (G : SimpleGraph V) (pins : Finset V) (color : V → Fin 3) (k : Fin 3) : Finset G.ConnectedComponent := by
  classical
  exact univ.filter (fun c ↦ ¬ComponentPinned G pins c ∧ Missing G color k c)

theorem free_components_card_bound (G : SimpleGraph V) (pins : Finset V) (color : V → Fin 3)
    (M : ℕ) (hM : ∀ k, (missingComponents G pins color k).card ≤ M) :
    (unpinnedComponents G pins).card ≤ (fullComponents G pins color).card + 3 * M := by
  classical
  have hsubset : unpinnedComponents G pins ⊆ fullComponents G pins color ∪
      univ.biUnion (missingComponents G pins color) := by
    intro c hc
    have hfree := (mem_unpinnedComponents G).mp hc
    by_cases hfull : Full G color c
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hfree, hfull⟩)
    · have hmissing : ∃ k, Missing G color k c := by
        simp only [Full, not_forall, not_exists, not_and] at hfull
        exact hfull
      obtain ⟨k, hk⟩ := hmissing
      exact mem_union_right _ (mem_biUnion.mpr ⟨k, mem_univ _, mem_filter.mpr ⟨mem_univ _, hfree, hk⟩⟩)
  have hcard := (card_le_card hsubset).trans (card_union_le _ _)
  have hunion := card_biUnion_le_card_mul (univ : Finset (Fin 3)) (missingComponents G pins color) M (fun k _ ↦ hM k)
  simp only [card_univ, Fintype.card_fin] at hunion
  omega

theorem residual_rank_bound (color : V → Fin 3) (data : V → ℕ → F₂) (H : ℕ)
    (rows : LargePrime H → Finset V) (hrows : ∀ p, (rows p).card ≤ 3)
    (hrow : ∀ (p : LargePrime H) (f : V → F₂), parityMap data f p.val = ∑ v ∈ rows p, f v)
    (hnonprime : ∀ (p : ℕ), ¬p.Prime → ∀ v, data v p = 0) (hrigid : PairwiseRigid color data)
    {D : Finset V} (hD : IsCover rows D) (R : Submodule F₂ (V → F₂)) (hR : R ≤ rowSolutions rows) :
    Module.finrank F₂ (CoordinateRestrictionRank.zeroed R D) ≤
      (fullComponents (graph rows D) (pins rows D) color).card + 3 * (primeCount H + 2) := by
  classical
  have hrank := CoverGraphResolution.residual_rank_bound hrows hD R hR
  rw [card_unpinnedComponents] at hrank
  have hmissing : ∀ k, (missingComponents (graph rows D) (pins rows D) color k).card ≤ primeCount H + 2 := by
    intro k
    apply missing_components_card_bound color data H rows hrows hrow hnonprime hrigid hD k
      (missingComponents (graph rows D) (pins rows D) color k)
    · intro c hc
      exact (mem_filter.mp hc).2.1
    · intro c hc
      exact (mem_filter.mp hc).2.2
  exact hrank.trans (free_components_card_bound _ _ color (primeCount H + 2) hmissing)

theorem free_component_prime_sum (data : V → ℕ → F₂) (H : ℕ)
    (rows : LargePrime H → Finset V) (hrows : ∀ p, (rows p).card ≤ 3)
    (hrow : ∀ (p : LargePrime H) (f : V → F₂), parityMap data f p.val = ∑ v ∈ rows p, f v)
    {D : Finset V} (hD : IsCover rows D) (c : (graph rows D).ConnectedComponent)
    (hfree : ¬ComponentPinned (graph rows D) (pins rows D) c) (p : LargePrime H) :
    (∑ v ∈ univ.filter (fun v ↦ (graph rows D).connectedComponentMk v = c), data v p.val) = 0 := by
  classical
  let f : ({c} : Finset (graph rows D).ConnectedComponent) → F₂ := fun _ ↦ 1
  let g := selection (graph rows D) {c} f
  have hfree' : ∀ z ∈ ({c} : Finset (graph rows D).ConnectedComponent),
      ¬ComponentPinned (graph rows D) (pins rows D) z := by
    intro z hz
    simpa only [mem_singleton.mp hz] using hfree
  have hg := selection_mem_zeroed_rows hrows hD {c} hfree' f
  have heq := hrow p g
  have hid : parityMap data g p.val =
      ∑ v ∈ univ.filter (fun v ↦ (graph rows D).connectedComponentMk v = c), data v p.val := by
    simp [g, f, parityMap, selection, Finset.sum_filter]
  rw [hid] at heq
  exact heq.trans (hg.1 p)

end PaperP1.ThreeBlockComponents
