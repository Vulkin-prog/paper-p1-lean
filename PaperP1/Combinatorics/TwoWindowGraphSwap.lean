module

public import PaperP1.Arithmetic.TwoBlockComponentPatterns

/-! # Swapping the two actual arithmetic windows preserves the pinned graph -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoWindowGraphSwap

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeOccurrences
  PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.TwoBlockComponentSquares

theorem label_swap (x y L : ℕ) (v : Occurrence L) :
    twoStartCompleteVertexLabel y x L (Sum.swap v) = twoStartCompleteVertexLabel x y L v := by
  cases v <;> rfl

theorem mem_occurrences_swap (x y L p : ℕ) (v : Occurrence L) :
    Sum.swap v ∈ primeOccurrences y x L p ↔ v ∈ primeOccurrences x y L p := by
  simp only [mem_primeOccurrences, label_swap]

theorem occurrences_swap (x y L p : ℕ) :
    primeOccurrences y x L p = (primeOccurrences x y L p).image Sum.swap := by
  classical
  ext v
  constructor
  · intro hv
    exact mem_image.mpr ⟨Sum.swap v, (mem_occurrences_swap y x L p v).mpr hv, Sum.swap_swap v⟩
  · rintro hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    exact (mem_occurrences_swap x y L p w).mpr hw

def iso (x y L : ℕ) : largePrimeGraph x y L ≃g largePrimeGraph y x L where
  toEquiv := Equiv.sumComm _ _
  map_rel_iff' := by
    intro v w
    change ((largePrimeGraph y x L).Adj (Sum.swap v) (Sum.swap w)) ↔ _
    have hneq : Sum.swap v ≠ Sum.swap w ↔ v ≠ w := by
      constructor
      · intro h he
        exact h (congrArg Sum.swap he)
      · intro h he
        apply h
        simpa only [Sum.swap_swap] using congrArg Sum.swap he
    simp only [largePrimeGraph_adj, mem_occurrences_swap, hneq]

def componentEquiv (x y L : ℕ) :
    (largePrimeGraph x y L).ConnectedComponent ≃ (largePrimeGraph y x L).ConnectedComponent :=
  (iso x y L).connectedComponentEquiv

theorem pinned_forward (x y L : ℕ) (v : Occurrence L) (hv : IsPinned x y L v) :
    IsPinned y x L (Sum.swap v) := by
  obtain ⟨p, hp, heq⟩ := hv
  refine ⟨p, hp, ?_⟩
  rw [occurrences_swap, heq, image_singleton]

theorem pinned_swap (x y L : ℕ) (v : Occurrence L) :
    IsPinned y x L (Sum.swap v) ↔ IsPinned x y L v := by
  constructor
  · intro h
    simpa only [Sum.swap_swap] using pinned_forward y x L (Sum.swap v) h
  · exact pinned_forward x y L v

theorem mem_vertices_swap (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (v : Occurrence L) :
    Sum.swap v ∈ vertices y x L (componentEquiv x y L c) ↔ v ∈ vertices x y L c := by
  simp only [vertices, MediumPrimeColumns.mem_componentVertices]
  exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp (φ := iso x y L)

theorem left_vertices_swap (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (vertices y x L (componentEquiv x y L c)).toLeft = (vertices x y L c).toRight := by
  ext i
  rw [mem_toLeft, mem_toRight]
  exact mem_vertices_swap x y L c (Sum.inr i)

theorem right_vertices_swap (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    (vertices y x L (componentEquiv x y L c)).toRight = (vertices x y L c).toLeft := by
  ext i
  rw [mem_toRight, mem_toLeft]
  exact mem_vertices_swap x y L c (Sum.inl i)

theorem component_pinned_forward (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent)
    (hc : ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c) :
    ComponentPinned (largePrimeGraph y x L) (pinnedVertices y x L) (componentEquiv x y L c) := by
  obtain ⟨v, hv, he⟩ := hc
  refine ⟨Sum.swap v, mem_pinnedVertices.mpr (pinned_forward x y L v (mem_pinnedVertices.mp hv)), ?_⟩
  exact (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp (φ := iso x y L)).mpr he

theorem component_pinned_swap (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    ComponentPinned (largePrimeGraph y x L) (pinnedVertices y x L) (componentEquiv x y L c) ↔
      ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c := by
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨Sum.swap v, ?_, ?_⟩
    · exact mem_pinnedVertices.mpr ((pinned_swap x y L (Sum.swap v)).mp
        (by simpa only [Sum.swap_swap] using mem_pinnedVertices.mp hv))
    · apply (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp (φ := iso x y L)).mp
      change (largePrimeGraph y x L).connectedComponentMk (Sum.swap (Sum.swap v)) =
        componentEquiv x y L c
      simpa only [Sum.swap_swap] using he
  · exact component_pinned_forward x y L c

end PaperP1.TwoWindowGraphSwap
