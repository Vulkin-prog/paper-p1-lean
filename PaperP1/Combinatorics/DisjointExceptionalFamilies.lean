module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-! # Actual disjoint families meeting a finite exceptional set are at most that set's cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointExceptionalFamilies

open Finset

variable {ι α : Type*} [Fintype ι]

def bad (I : ι → Finset α) (B : Finset α) : Finset ι := by
  classical
  exact univ.filter fun ν ↦ ∃ z ∈ I ν, z ∈ B

theorem mem_bad (I : ι → Finset α) (B : Finset α) (ν : ι) :
    ν ∈ bad I B ↔ ∃ z ∈ I ν, z ∈ B := by
  classical
  simp only [bad, mem_filter, mem_univ, true_and]

theorem card_bad_le (I : ι → Finset α) (B : Finset α)
    (hdisj : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) : (bad I B).card ≤ B.card := by
  classical
  choose z hzI hzB using (fun ν : bad I B ↦ (mem_bad I B ν).mp ν.property)
  let f : bad I B → B := fun ν ↦ ⟨z ν, hzB ν⟩
  have hf : Function.Injective f := by
    intro ν μ h
    have heq : z ν = z μ := congrArg Subtype.val h
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (hzI ν) (heq ▸ hzI μ)
  exact Finset.card_le_card_of_injective hf

theorem regular (I : ι → Finset α) (B : Finset α) (ν : ι) (hν : ν ∉ bad I B) :
    ∀ z ∈ I ν, z ∉ B := by
  intro z hz hB
  exact hν ((mem_bad I B ν).mpr ⟨z, hz, hB⟩)

end PaperP1.DisjointExceptionalFamilies
