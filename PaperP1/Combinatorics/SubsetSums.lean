module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Insertion recurrences for sums over subsets of a fixed size -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.SubsetSums

open Finset

variable {ι A : Type*} [DecidableEq ι] [AddCommMonoid A]

omit [DecidableEq ι] in
theorem one (G : Finset ι) (f : Finset ι → A) :
    (∑ I ∈ G.powersetCard 1, f I) = ∑ x ∈ G, f {x} := by
  rw [powersetCard_one, sum_map]
  rfl

theorem succ_insert (G : Finset ι) (x : ι) (hx : x ∉ G) (r : ℕ) (f : Finset ι → A) :
    (∑ I ∈ (insert x G).powersetCard (r + 1), f I) =
      (∑ I ∈ G.powersetCard (r + 1), f I) + ∑ I ∈ G.powersetCard r, f (insert x I) := by
  have hdisj : Disjoint (G.powersetCard (r + 1)) ((G.powersetCard r).image (insert x)) := by
    apply disjoint_left.mpr
    intro I hI hI'
    obtain ⟨J, _, rfl⟩ := mem_image.mp hI'
    exact hx ((mem_powersetCard.mp hI).1 (mem_insert_self x J))
  rw [powersetCard_succ_insert hx r, sum_union hdisj]
  congr 1
  apply sum_image
  intro I hI J hJ hij
  have hxi : x ∉ I := fun h ↦ hx ((mem_powersetCard.mp hI).1 h)
  have hxj : x ∉ J := fun h ↦ hx ((mem_powersetCard.mp hJ).1 h)
  simpa only [erase_insert hxi, erase_insert hxj] using congrArg (fun K ↦ K.erase x) hij

end PaperP1.SubsetSums
