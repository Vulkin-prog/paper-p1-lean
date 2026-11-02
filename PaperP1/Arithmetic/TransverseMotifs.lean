module

public import PaperP1.Combinatorics.BoundedSubsets
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Prod

/-! # Finite transverse motifs and their exact three-block decomposition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransverseMotifs

open Finset

abbrev Vertex (L : ℕ) := Fin 3 × Fin (L + 1)

def offsets {L : ℕ} (E : Finset (Vertex L)) (i : Fin 3) : Finset (Fin (L + 1)) :=
  univ.filter fun u ↦ (i, u) ∈ E

def Transverse {L : ℕ} (E : Finset (Vertex L)) : Prop := ∀ i : Fin 3, (offsets E i).Nonempty

def pool (L d : ℕ) : Finset (Finset (Vertex L)) := BoundedSubsets.sets univ d

theorem mem_offsets {L : ℕ} (E : Finset (Vertex L)) (i : Fin 3) (u : Fin (L + 1)) :
    u ∈ offsets E i ↔ (i, u) ∈ E := by simp only [offsets, mem_filter, mem_univ, true_and]

theorem slice_image {L : ℕ} (E : Finset (Vertex L)) (i : Fin 3) :
    (E.filter fun v ↦ v.1 = i) = (offsets E i).image (fun u ↦ (i, u)) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨hvE, hi⟩ := mem_filter.mp hv
    have heq : v = (i, v.2) := Prod.ext hi rfl
    exact mem_image.mpr ⟨v.2, (mem_offsets E i v.2).mpr (by rwa [← heq]), heq.symm⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨(mem_offsets E i u).mp hu, rfl⟩

theorem slice_card {L : ℕ} (E : Finset (Vertex L)) (i : Fin 3) :
    (E.filter fun v ↦ v.1 = i).card = (offsets E i).card := by
  rw [slice_image]
  exact card_image_of_injective _ (fun _ _ hh ↦ congrArg Prod.snd hh)

theorem slice_product {L : ℕ} {M : Type*} [CommMonoid M] (E : Finset (Vertex L))
    (i : Fin 3) (f : Vertex L → M) :
    (∏ v ∈ E.filter (fun v ↦ v.1 = i), f v) = ∏ u ∈ offsets E i, f (i, u) := by
  rw [slice_image, prod_image (fun _ _ _ _ hh ↦ congrArg Prod.snd hh)]

theorem product_decomposition {L : ℕ} {M : Type*} [CommMonoid M] (E : Finset (Vertex L))
    (f : Vertex L → M) :
    (∏ v ∈ E, f v) =
      (∏ u ∈ offsets E 0, f (0, u)) * (∏ v ∈ offsets E 1, f (1, v)) *
        (∏ w ∈ offsets E 2, f (2, w)) := by
  have hh := prod_fiberwise E Prod.fst f
  simpa only [Fin.prod_univ_three, slice_product] using hh.symm

theorem card_decomposition {L : ℕ} (E : Finset (Vertex L)) :
    E.card = (offsets E 0).card + (offsets E 1).card + (offsets E 2).card := by
  have hh := card_eq_sum_card_fiberwise (s := E) (t := (univ : Finset (Fin 3)))
    (f := Prod.fst) (fun _ _ ↦ mem_univ _)
  simpa only [Fin.sum_univ_three, slice_card] using hh

theorem first_two_card_le {L : ℕ} (E : Finset (Vertex L)) :
    (offsets E 0).card + (offsets E 1).card ≤ E.card := by
  have hh := card_decomposition E
  omega

theorem offsets_pairwise_disjoint {ι : Type*} [DecidableEq ι] {L : ℕ} (I : Finset ι)
    (E : ι → Finset (Vertex L)) (hE : (↑I : Set ι).PairwiseDisjoint E) (i : Fin 3) :
    (↑I : Set ι).PairwiseDisjoint (fun j ↦ offsets (E j) i) := by
  intro j hj k hk hjk
  apply disjoint_left.mpr
  intro u huj huk
  exact disjoint_left.mp (hE hj hk hjk) ((mem_offsets _ _ _).mp huj) ((mem_offsets _ _ _).mp huk)

theorem mem_pool (L d : ℕ) (E : Finset (Vertex L)) : E ∈ pool L d ↔ E.card ≤ d := by
  simp only [pool, BoundedSubsets.mem_sets, subset_univ, true_and]

theorem card_pool (L d : ℕ) : (pool L d).card ≤ (d + 1) * (3 * (L + 1) + 1) ^ d := by
  simpa only [pool, card_univ, Fintype.card_prod, Fintype.card_fin] using
    BoundedSubsets.card_sets (univ : Finset (Vertex L)) d

end PaperP1.TransverseMotifs
