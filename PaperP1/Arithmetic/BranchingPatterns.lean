module

public import PaperP1.Arithmetic.EvenSquareClasses

/-! # Concrete fixed dilations and injective reindexing of exceptional sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BranchingPatterns

open Finset PaperP1.Arithmetic

def dilationIndices {k L : ℕ} (a d : ℕ) (hfit : a + d * k ≤ L) : Fin (k + 1) → Fin (L + 1) :=
  fun i ↦ ⟨a + d * i.val, by have h := Nat.mul_le_mul_left d (show i.val ≤ k by omega); omega⟩

theorem dilationIndices_injective {k L : ℕ} (a d : ℕ) (hd : 0 < d) (hfit : a + d * k ≤ L) :
    Function.Injective (dilationIndices a d hfit) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  change a + d * i.val = a + d * j.val at h
  nlinarith

theorem dilation_label {x k L : ℕ} (hx : 0 < x) (a d : ℕ) (hfit : a + d * k ≤ L) (i : Fin (k + 1)) :
    Affine.startCompleteVertexLabel x L (dilationIndices a d hfit i) = x - 1 + a + d * i.val := by
  rw [startCompleteVertexLabel_eq_offset hx]
  change x - 1 + (a + d * i.val) = _
  omega

def pullExceptions {ι : Type*} (G : Finset ι) (φ : ι → ℕ) (E : Finset ℕ) : Finset ι := G.filter fun z ↦ φ z ∈ E

theorem pullExceptions_subset {ι : Type*} (G : Finset ι) (φ : ι → ℕ) (E : Finset ℕ) :
    pullExceptions G φ E ⊆ G := filter_subset _ _

theorem pullExceptions_card {ι : Type*} (G : Finset ι) (φ : ι → ℕ) (E : Finset ℕ)
    (hφ : Set.InjOn φ G) : (pullExceptions G φ E).card ≤ E.card := by
  apply card_le_card_of_injOn φ
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro z hz z' hz' hzz
    exact hφ (mem_filter.mp hz).1 (mem_filter.mp hz').1 hzz

theorem notMem_pullExceptions {ι : Type*} {G : Finset ι} {φ : ι → ℕ} {E : Finset ℕ} {z : ι}
    (hz : z ∈ G) (hnot : z ∉ pullExceptions G φ E) : φ z ∉ E := by
  intro h
  exact hnot (mem_filter.mpr ⟨hz, h⟩)

def observationValues {j L : ℕ} (n : Fin j → Fin (L + 1) → ℕ) : Finset ℕ :=
  univ.image (fun p : Fin j × Fin (L + 1) ↦ n p.1 p.2)

theorem observationValues_card {j L : ℕ} (n : Fin j → Fin (L + 1) → ℕ) :
    (observationValues n).card ≤ j * (L + 1) := by
  exact card_image_le.trans_eq (by simp)

theorem observationValues_bounds {j L X : ℕ} (n : Fin j → Fin (L + 1) → ℕ)
    (hn : ∀ i v, 1 ≤ n i v ∧ n i v ≤ X) :
    ∀ r ∈ observationValues n, 1 ≤ r ∧ r ≤ X := by
  intro r hr
  obtain ⟨⟨i, v⟩, _, rfl⟩ := mem_image.mp hr
  exact hn i v

end PaperP1.BranchingPatterns
