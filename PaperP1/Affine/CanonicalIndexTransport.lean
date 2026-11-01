module

public import PaperP1.Affine.CanonicalPartConnected

/-! # Connectedness and relative nullity survive a bijection of actual indices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalIndexTransport

open Finset PaperP1.Affine PaperP1.CanonicalPartConnected

variable {U ι κ : Type*} [AddCommGroup U] [Module 𝔽₂ U]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (T : κ → Submodule 𝔽₂ U) (e : ι ≃ κ)

theorem connected_reindex [Nonempty ι] [Nonempty κ]
    (hconnected : canonicalRelationPartition (fun i : ι ↦ T (e i)) = ⊤) :
    canonicalRelationPartition T = ⊤ := by
  classical
  apply (connected_iff_noCut T).mpr
  intro D hD hrest hcut
  let J := (univ : Finset ι).filter fun i ↦ e i ∈ D
  obtain ⟨d, hd⟩ := hD
  have hJ : J.Nonempty := ⟨e.symm d, mem_filter.mpr ⟨mem_univ _, by simpa only [e.apply_symm_apply] using hd⟩⟩
  obtain ⟨k, hk⟩ := hrest
  have hknot : k ∉ D := (mem_sdiff.mp hk).2
  have hJrest : ((univ : Finset ι) \ J).Nonempty := by
    refine ⟨e.symm k, mem_sdiff.mpr ⟨mem_univ _, ?_⟩⟩
    intro hmem
    have h := (mem_filter.mp hmem).2
    exact hknot (by simpa only [e.apply_symm_apply] using h)
  apply ((connected_iff_noCut (fun i : ι ↦ T (e i))).mp hconnected) J hJ hJrest
  intro s hs
  let t : (k : κ) → T k := fun k ↦
    ⟨(s (e.symm k)).val, by simpa only [e.apply_symm_apply] using (s (e.symm k)).property⟩
  have ht : relationAddition T t = 0 := by
    change (∑ k : κ, (s (e.symm k)).val) = 0
    change (∑ i : ι, (s i).val) = 0 at hs
    exact (e.symm.sum_comp (fun i : ι ↦ (s i).val)).trans hs
  have hzero := hcut t ht
  have hsum := e.symm.sum_comp (fun i : ι ↦ if e i ∈ D then (s i).val else 0)
  simp only [e.apply_symm_apply] at hsum
  have hcutSum : (∑ i ∈ J, (s i).val) = ∑ k ∈ D, (t k).val := by
    simpa only [J, t, ← sum_filter, filter_mem_eq_inter, univ_inter] using hsum.symm
  exact hcutSum.trans hzero

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem span_reindex : (⨆ i : ι, T (e i)) = ⨆ k : κ, T k := by
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup T (e i)
  · refine iSup_le fun k ↦ ?_
    have h := le_iSup (fun i : ι ↦ T (e i)) (e.symm k)
    simpa only [e.apply_symm_apply] using h

omit [DecidableEq ι] [DecidableEq κ] in
theorem nullity_reindex [∀ k, Fintype (T k)] :
    relativeNullity (fun i : ι ↦ T (e i)) = relativeNullity T := by
  rw [relativeNullity_eq_dimension_deficit, relativeNullity_eq_dimension_deficit, span_reindex T e]
  rw [e.sum_comp (fun k : κ ↦ Module.finrank 𝔽₂ (T k))]

end PaperP1.CanonicalIndexTransport
