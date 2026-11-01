module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-! # Minimal finite covers and private vertices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MinimalFiniteCover

open Finset

variable {V : Type*} [DecidableEq V]

theorem exists_private_cover (A : Finset (Finset V)) (D : Finset V) (hcover : A.biUnion id = D) :
    ∃ F ⊆ A, F.biUnion id = D ∧ ∀ e ∈ F, ∃ v ∈ e,
      ∀ f ∈ F, v ∈ f → f = e := by
  classical
  let C := A.powerset.filter (fun F : Finset (Finset V) ↦ F.biUnion id = D)
  have hAC : A ∈ C := mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hcover⟩
  obtain ⟨F, hFC, hmin⟩ := exists_min_image C Finset.card ⟨A, hAC⟩
  obtain ⟨hFA, hFD⟩ := mem_filter.mp hFC
  refine ⟨F, mem_powerset.mp hFA, hFD, ?_⟩
  intro e he
  by_contra hnot
  have hw : ∀ v ∈ e, ∃ f ∈ F, f ≠ e ∧ v ∈ f := by
    intro v hv
    by_contra hex
    apply hnot
    refine ⟨v, hv, ?_⟩
    intro f hf hvf
    by_contra hfe
    exact hex ⟨f, hf, hfe, hvf⟩
  have hsame : (F.erase e).biUnion id = F.biUnion id := by
    apply subset_antisymm
    · intro v hv
      obtain ⟨f, hf, hvf⟩ := mem_biUnion.mp hv
      exact mem_biUnion.mpr ⟨f, (erase_subset e F) hf, hvf⟩
    · intro v hv
      obtain ⟨f, hf, hvf⟩ := mem_biUnion.mp hv
      by_cases hfe : f = e
      · obtain ⟨g, hg, hge, hvg⟩ := hw v (hfe ▸ hvf)
        exact mem_biUnion.mpr ⟨g, mem_erase.mpr ⟨hge, hg⟩, hvg⟩
      · exact mem_biUnion.mpr ⟨f, mem_erase.mpr ⟨hfe, hf⟩, hvf⟩
  have hnext : F.erase e ∈ C := mem_filter.mpr
    ⟨mem_powerset.mpr ((erase_subset e F).trans (mem_powerset.mp hFA)), hsame.trans hFD⟩
  have hcontra := hmin (F.erase e) hnext
  rw [card_erase_of_mem he] at hcontra
  have hpos : 0 < F.card := card_pos.mpr ⟨e, he⟩
  omega

end PaperP1.MinimalFiniteCover
