module

public import PaperP1.Combinatorics.ComponentSelection
public import PaperP1.Coding.SmallComponentBound

/-! # Actual value sets on free components of the omitted-prime graph -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeRowComponents

open Finset PaperP1.Arithmetic PaperP1.PinnedGraphResolution

local instance primeRowPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance primeRowDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def rows (S P : Finset ℕ) (p : ℕ) : Finset S :=
  if p ∈ P then ∅ else univ.filter fun n ↦ parityVec n.val p ≠ 0

def graph (S P : Finset ℕ) : SimpleGraph S := CoverGraphResolution.graph (rows S P) ∅

def pins (S P : Finset ℕ) : Finset S := CoverGraphResolution.pins (rows S P) ∅

def vertices (S P : Finset ℕ) (c : (graph S P).ConnectedComponent) : Finset S :=
  univ.filter fun n ↦ (graph S P).connectedComponentMk n = c

def values (S P : Finset ℕ) (c : (graph S P).ConnectedComponent) : Finset ℕ :=
  (vertices S P c).image Subtype.val

theorem mem_values {S P : Finset ℕ} {c : (graph S P).ConnectedComponent} {n : ℕ} :
    n ∈ values S P c ↔ ∃ v : S, v.val = n ∧ (graph S P).connectedComponentMk v = c := by
  simp only [values, mem_image, vertices, mem_filter, mem_univ, true_and]
  exact exists_congr fun _ ↦ and_comm

theorem values_subset (S P : Finset ℕ) (c : (graph S P).ConnectedComponent) : values S P c ⊆ S := by
  intro n hn
  obtain ⟨v, rfl, _⟩ := mem_values.mp hn
  exact v.property

theorem values_nonempty (S P : Finset ℕ) (c : (graph S P).ConnectedComponent) :
    (values S P c).Nonempty :=
  ⟨c.out.val, mem_values.mpr ⟨c.out, rfl, c.out_eq⟩⟩

theorem values_disjoint (S P : Finset ℕ) :
    Pairwise (fun c d : (graph S P).ConnectedComponent ↦ Disjoint (values S P c) (values S P d)) := by
  intro c d hcd
  apply disjoint_left.mpr
  intro n hnc hnd
  obtain ⟨v, hv, hc⟩ := mem_values.mp hnc
  obtain ⟨w, hw, hd⟩ := mem_values.mp hnd
  have hvw : v = w := Subtype.ext (hv.trans hw.symm)
  exact hcd (hc.symm.trans (hvw ▸ hd))

theorem values_card (S P : Finset ℕ) (c : (graph S P).ConnectedComponent) :
    (values S P c).card = Fintype.card c.supp := by
  rw [values, card_image_of_injective _ Subtype.val_injective]
  have heq : vertices S P c = c.supp.toFinset := by
    ext v
    simp only [vertices, mem_filter, mem_univ, true_and, Set.mem_toFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [heq, Set.toFinset_card]

theorem empty_cover {S P : Finset ℕ} (hrows : ∀ p, (rows S P p).card ≤ 2) :
    CoverGraphResolution.IsCover (rows S P) ∅ := by
  intro p hp
  have := hrows p
  omega

theorem sum_row {S P : Finset ℕ} (p : ℕ) (hp : p ∉ P) (u : S → F₂) :
    (∑ v ∈ rows S P p, u v) = ∑ v : S, u v * parityVec v.val p := by
  rw [rows, ite_eq_right hp, sum_filter]
  apply sum_congr rfl
  intro v _
  by_cases hv : parityVec v.val p = 0
  · simp only [hv, ne_eq, not_true_eq_false, ite_false, mul_zero]
  · rw [ite_eq_left hv, HammingBound.eq_one_of_ne_zero _ hv, mul_one]

theorem free_component_parity {S P : Finset ℕ} (hrows : ∀ p, (rows S P p).card ≤ 2)
    (c : (graph S P).ConnectedComponent) (hc : ¬ComponentPinned (graph S P) (pins S P) c)
    (p : ℕ) (hp : p ∉ P) : ∑ n ∈ values S P c, parityVec n p = 0 := by
  have hrows3 : ∀ p, (rows S P p).card ≤ 3 := fun p ↦ (hrows p).trans (by omega)
  have hfree : ∀ d ∈ ({c} : Finset (graph S P).ConnectedComponent),
      ¬ComponentPinned (graph S P) (pins S P) d := by
    intro d hd
    simpa only [mem_singleton.mp hd] using hc
  have hsel := ComponentSelection.selection_mem_zeroed_rows hrows3 (empty_cover hrows) {c} hfree
    (fun _ ↦ (1 : F₂))
  have hrow := hsel.1 p
  change (∑ v ∈ rows S P p, ComponentSelection.selection (graph S P) {c} (fun _ ↦ (1 : F₂)) v) = 0 at hrow
  have hvalue (v : S) : ComponentSelection.selection (graph S P) {c} (fun _ ↦ (1 : F₂)) v =
      if (graph S P).connectedComponentMk v = c then 1 else 0 := by
    by_cases hv : (graph S P).connectedComponentMk v = c <;>
      simp [ComponentSelection.selection, mem_singleton, hv]
  have hrow' : (∑ v : S, if parityVec v.val p ≠ 0 then
      (if (graph S P).connectedComponentMk v = c then (1 : F₂) else 0) else 0) = 0 := by
    simpa only [rows, ite_eq_right hp, sum_filter, hvalue] using hrow
  calc
    _ = ∑ v : S, if (graph S P).connectedComponentMk v = c then parityVec v.val p else 0 := by
      rw [values, sum_image]
      · rw [vertices, sum_filter]
      · exact fun _ _ _ _ h ↦ Subtype.ext h
    _ = ∑ v : S, if parityVec v.val p ≠ 0 then
        (if (graph S P).connectedComponentMk v = c then (1 : F₂) else 0) else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases hv : (graph S P).connectedComponentMk v = c
      · by_cases hpv : parityVec v.val p = 0
        · simp [hv, hpv]
        · simp [hv, HammingBound.eq_one_of_ne_zero _ hpv]
      · simp [hv]
    _ = 0 := hrow'

end PaperP1.PrimeRowComponents
