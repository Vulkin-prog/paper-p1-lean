module

public import PaperP1.Model.DirectRunBlocks
public import PaperP1.Model.IndependentExtensionDeficit

/-! # Every proper nonempty source of a connected family has a failed direct complement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedComplementDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem not_direct (L : ℕ) (I D : Finset ℕ) (hproper : D ⊂ I) (hD : D.Nonempty)
    (hconn : Connected L I) :
    ¬ PaperP1.IndependentExtensionDeficit.Direct (span (fun x ↦ squareClassSpace x L) D) L (I \ D) := by
  classical
  let S := fun x ↦ squareClassSpace x L
  let W := span S D
  let : Fintype W := PaperP1.MinimalRelativeRelations.spanFintype S D
  have hDI : D ⊆ I := hproper.subset
  have hcompNe : (I \ D).Nonempty := sdiff_nonempty.mpr (ssubset_iff_subset_not_subset.mp hproper).2
  have hdis : Disjoint D (I \ D) := disjoint_left.mpr
    (fun x hxD hxcomp ↦ (mem_sdiff.mp hxcomp).2 hxD)
  have hunion : D ∪ (I \ D) = I := union_sdiff_of_subset hDI
  intro hdirect
  have hz := (PaperP1.IndependentExtensionDeficit.direct_iff_nullity W L (I \ D)).mp hdirect
  have hcompressed := (PaperP1.MinimalRelativeRelations.zero_iff_compressed S D (I \ D) hdis).mp hz
  have hnull : runRelativeNullity L I = runRelativeNullity L D := by
    simpa only [S, hunion, runRelativeNullity] using hcompressed.2
  have hrestricted := PaperP1.RetainedNullity.compressed_restriction S D I (I \ D) hDI sdiff_subset hnull
  have hinter : (I \ D) ∩ D = ∅ := disjoint_iff_inter_eq_empty.mp hdis.symm
  have hzero : runRelativeNullity L (I \ D) = 0 := by
    simpa only [S, hinter, relativeNullityOn_empty, runRelativeNullity] using hrestricted
  have hnulladd : runRelativeNullity L (D ∪ (I \ D)) =
      runRelativeNullity L D + runRelativeNullity L (I \ D) := by
    rw [hunion, hnull, hzero, add_zero]
  have hnot := PaperP1.DirectRunBlocks.not_connected L D (I \ D) hD hcompNe hdis hnulladd
  exact hnot (by simpa only [hunion] using hconn)

theorem complement_mem (G : Finset ℕ) (L : ℕ) (I D : Finset ℕ)
    (hIG : I ⊆ G) (hproper : D ⊂ I) (hD : D.Nonempty) (hconn : Connected L I) :
    I \ D ∈ PaperP1.IndependentExtensionDeficit.families (G \ D)
      (span (fun x ↦ squareClassSpace x L) D) L := by
  apply (PaperP1.IndependentExtensionDeficit.mem_families _ _ _ _).mpr
  exact ⟨sdiff_subset_sdiff_left D hIG, not_direct L I D hproper hD hconn⟩

end PaperP1.ConnectedComplementDeficit
