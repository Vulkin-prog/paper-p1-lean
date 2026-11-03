module

public import PaperP1.Combinatorics.DisjointOffsetGrid

/-! # An arbitrary requested number of actual distinct disjoint-family grid points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointOffsetGridSelection

open Finset

theorem select_n {ι : Type*} (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (a n : ℕ)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a) (hn : n ≤ A.card * a) :
    ∃ x y : Fin n → ℤ, Function.Injective x ∧
      ∀ t, ∃ ν ∈ A, x t ∈ I ν ∧ y t = j ν := by
  classical
  have hc : n ≤ (DisjointOffsetGrid.points A I j).card := by
    rw [DisjointOffsetGrid.card_points A I j a hdisj hcard]
    exact hn
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin n) (s := DisjointOffsetGrid.points A I j) (by simpa only [Fintype.card_fin] using hc)
  have hem (t) : e t ∈ DisjointOffsetGrid.points A I j := he ⟨t, rfl⟩
  refine ⟨fun t ↦ (e t).1, fun t ↦ (e t).2, ?_, ?_⟩
  · intro t u htu
    exact e.injective (DisjointOffsetGrid.fst_injective A I j hdisj (hem t) (hem u) htu)
  · intro t
    obtain ⟨ν, hν, himage⟩ := mem_biUnion.mp (hem t)
    obtain ⟨x, hx, heq⟩ := mem_image.mp himage
    have hfirst : x = (e t).1 := congrArg Prod.fst heq
    refine ⟨ν, hν, ?_, (congrArg Prod.snd heq).symm⟩
    change (e t).1 ∈ I ν
    rw [← hfirst]
    exact hx

end PaperP1.DisjointOffsetGridSelection
