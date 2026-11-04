module

public import PaperP1.Arithmetic.AsymmetricEnvelopeGraph
public import PaperP1.Arithmetic.ForwardSubsetEmbedding
public import PaperP1.Arithmetic.SubsetEvenLoss

/-! # Two prescribed finite blocks with every unused envelope coordinate pinned

The target budget is the cardinality of the actual new set, independently
of the width of its enclosing interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetEnvelopeGraph

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution PaperP1.LargePrimeOccurrences
  PaperP1.AsymmetricEnvelopeGraph

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def newPins (y H R : ℕ) (V : Finset ℕ) : Finset (Occurrence H) :=
  (univ.filter fun j : Fin (H + 1) ↦ startCompleteVertexLabel (start y R) H j ∉ V).image Sum.inr

def pins (x y H R : ℕ) (U V : Finset ℕ) : Finset (Occurrence H) :=
  (pinnedVertices (start x R) (start y R) H ∪ oldPins x H R U) ∪ newPins y H R V

def space (x y H R : ℕ) (U V : Finset ℕ) : Submodule F₂ (Occurrence H → F₂) :=
  PinnedGraphSpace (largePrimeGraph (start x R) (start y R) H) (pins x y H R U V)

def targets (y H R : ℕ) (V : Finset ℕ) : Finset (Occurrence H) :=
  (univ.filter fun j : Fin (H + 1) ↦ startCompleteVertexLabel (start y R) H j ∈ V).image Sum.inr

def index (y H R : ℕ) (V : Finset ℕ) (hV : V ⊆ Ico (y - R) (y - R + (H + 1))) : V ↪ Fin (H + 1) :=
  ForwardSubsetEmbedding.index (y - R) (H + 1) V hV

theorem index_label {y H R : ℕ} (hy : R < y) (V : Finset ℕ)
    (hV : V ⊆ Ico (y - R) (y - R + (H + 1))) (n : V) :
    startCompleteVertexLabel (start y R) H (index y H R V hV n) = n.val := by
  rw [label_eq hy]
  exact ForwardSubsetEmbedding.label (y - R) (H + 1) V hV n

theorem target_pins_cover (x y H R : ℕ) (U V : Finset ℕ) (j : Fin (H + 1)) :
    Sum.inr j ∈ targets y H R V ∪ pins x y H R U V := by
  by_cases hj : startCompleteVertexLabel (start y R) H j ∈ V
  · exact mem_union_left _ (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, rfl⟩)
  · exact mem_union_right _ (mem_union_right _ (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, rfl⟩))

theorem old_mem_of_unpinned {x y H R : ℕ} (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y H R U V) c) (i : Fin (H + 1))
    (hi : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inl i) = c) :
    startCompleteVertexLabel (start x R) H i ∈ U := by
  by_contra hn
  exact hfree ⟨Sum.inl i, mem_union_left _ (mem_union_right _
    (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hn⟩, rfl⟩)), hi⟩

theorem new_mem_of_unpinned {x y H R : ℕ} (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y H R U V) c) (j : Fin (H + 1))
    (hj : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr j) = c) :
    startCompleteVertexLabel (start y R) H j ∈ V := by
  by_contra hn
  exact hfree ⟨Sum.inr j, mem_union_right _
    (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hn⟩, rfl⟩), hj⟩

theorem original_unpinned {x y H R : ℕ} (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y H R U V) c) :
    ¬ComponentPinned _ (pinnedVertices (start x R) (start y R) H) c := by
  rintro ⟨v, hv, he⟩
  exact hfree ⟨v, mem_union_left _ (mem_union_left _ hv), he⟩

theorem targets_card_le {y H R : ℕ} (hy : R < y) (V : Finset ℕ) : (targets y H R V).card ≤ V.card := by
  let J := univ.filter fun j : Fin (H + 1) ↦ startCompleteVertexLabel (start y R) H j ∈ V
  have hinj := startCompleteVertexLabel_injective (x := start y R) (L := H)
    (by have hh := start_ge_two hy; omega)
  have hsub : J.image (startCompleteVertexLabel (start y R) H) ⊆ V := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    exact (mem_filter.mp hj).2
  calc
    _ = J.card := card_image_of_injective _ Sum.inr_injective
    _ = (J.image (startCompleteVertexLabel (start y R) H)).card := (card_image_of_injective _ hinj).symm
    _ ≤ _ := card_le_card hsub

end PaperP1.SubsetEnvelopeGraph
