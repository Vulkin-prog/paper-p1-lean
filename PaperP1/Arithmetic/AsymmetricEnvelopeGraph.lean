module

public import PaperP1.Combinatorics.LargePrimeGraphResolution
public import PaperP1.Arithmetic.AsymmetricEvenLoss
public import PaperP1.Algebra.FinitePiExtensionSupport

/-! # The actual envelope graph with every unused old and new coordinate pinned

The envelope is only a bookkeeping domain. Free components may use exactly
the prescribed old values and the ORIGINAL new window, never ghost vertices.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricEnvelopeGraph

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution PaperP1.LargePrimeOccurrences

def start (x R : ℕ) : ℕ := x - R + 1

def targetIndex (L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) : Fin (L + 1) ↪ Fin (H + 1) where
  toFun i := ⟨R - 1 + i.val, by have hi := i.isLt; omega⟩
  inj' := by intro i j he; apply Fin.ext; have hh := congrArg Fin.val he; dsimp at hh; omega

def targetPositions (L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) : Finset (Occurrence H) :=
  univ.image (fun i : Fin (L + 1) ↦ Sum.inr (targetIndex L H R hnew hamb i))

def oldPins (x H R : ℕ) (old : Finset ℕ) : Finset (Occurrence H) := by
  classical
  exact (univ.filter fun i : Fin (H + 1) ↦ startCompleteVertexLabel (start x R) H i ∉ old).image Sum.inl

def newPins (L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) : Finset (Occurrence H) := by
  classical
  exact (univ.filter fun j : Fin (H + 1) ↦ ∀ i, targetIndex L H R hnew hamb i ≠ j).image Sum.inr

def pins (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) : Finset (Occurrence H) :=
  (pinnedVertices (start x R) (start y R) H ∪ oldPins x H R old) ∪ newPins L H R hnew hamb

def space (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Submodule F₂ (Occurrence H → F₂) :=
  PinnedGraphSpace (largePrimeGraph (start x R) (start y R) H) (pins x y L H R hnew hamb old)

theorem start_ge_two {x R : ℕ} (hx : R < x) : 2 ≤ start x R := by dsimp [start]; omega

theorem label_eq {x R H : ℕ} (hx : R < x) (i : Fin (H + 1)) :
    startCompleteVertexLabel (start x R) H i = x - R + i.val := by
  rw [startCompleteVertexLabel_eq_offset (by have hh := start_ge_two hx; omega)]
  dsimp [start]

theorem target_label {y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H)
    (i : Fin (L + 1)) :
    startCompleteVertexLabel (start y R) H (targetIndex L H R hnew hamb i) = startCompleteVertexLabel y L i := by
  rw [label_eq hy, startCompleteVertexLabel_eq_offset (by omega : 0 < y)]
  dsimp [targetIndex]
  omega

theorem old_forward {x R H n : ℕ} (hx : R < x) (hamb : 2 * R ≤ H)
    (hn : |(n : ℤ) - x| ≤ (R : ℤ)) : n ∈ Ico (x - R) (x - R + (H + 1)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  apply mem_Ico.mpr
  omega

theorem targetPositions_card (L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) :
    (targetPositions L H R hnew hamb).card = L + 1 := by
  have hinj : Function.Injective (fun i : Fin (L + 1) ↦ Sum.inr (targetIndex L H R hnew hamb i) : Fin (L + 1) → Occurrence H) :=
    Sum.inr_injective.comp (targetIndex L H R hnew hamb).injective
  rw [targetPositions, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

theorem target_pins_cover (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (j : Fin (H + 1)) : Sum.inr j ∈ targetPositions L H R hnew hamb ∪ pins x y L H R hnew hamb old := by
  classical
  by_cases hj : ∃ i, targetIndex L H R hnew hamb i = j
  · obtain ⟨i, rfl⟩ := hj
    exact mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  · apply mem_union_right
    apply mem_union_right
    exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, fun i hi ↦ hj ⟨i, hi⟩⟩, rfl⟩

theorem old_mem_of_unpinned {x y L H R : ℕ} (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) (i : Fin (H + 1))
    (hi : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inl i) = c) :
    startCompleteVertexLabel (start x R) H i ∈ old := by
  classical
  by_contra hn
  apply hfree
  refine ⟨Sum.inl i, mem_union_left _ (mem_union_right _ ?_), hi⟩
  exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hn⟩, rfl⟩

theorem new_index_of_unpinned {x y L H R : ℕ} (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (pins x y L H R hnew hamb old) c) (j : Fin (H + 1))
    (hj : (largePrimeGraph (start x R) (start y R) H).connectedComponentMk (Sum.inr j) = c) :
    ∃ i, targetIndex L H R hnew hamb i = j := by
  classical
  by_contra hn
  apply hfree
  refine ⟨Sum.inr j, mem_union_right _ ?_, hj⟩
  exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, fun i hi ↦ hn ⟨i, hi⟩⟩, rfl⟩

end PaperP1.AsymmetricEnvelopeGraph
