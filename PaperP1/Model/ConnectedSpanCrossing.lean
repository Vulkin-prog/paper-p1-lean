module

public import PaperP1.Model.DirectRunBlocks
public import PaperP1.Affine.MinimalSpanCrossing

/-! # Every proper nonempty part of a connected family has an actual minimal crossing -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedSpanCrossing

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem cut (L : ℕ) (I D : Finset ℕ) (hproper : D ⊂ I) (hD : D.Nonempty)
    (hconn : ConnectedWindowFamilies.Connected L I) :
    span (fun x ↦ squareClassSpace x L) D ⊓
      span (fun x ↦ squareClassSpace x L) (I \ D) ≠ ⊥ := by
  classical
  intro hzero
  have hcompNe : (I \ D).Nonempty := sdiff_nonempty.mpr (ssubset_iff_subset_not_subset.mp hproper).2
  have hdis : Disjoint D (I \ D) := disjoint_left.mpr
    (fun x hxD hxcomp ↦ (mem_sdiff.mp hxcomp).2 hxD)
  have hnull := (DirectRunBlocks.additive_iff_spaces L D (I \ D) hdis).mpr (disjoint_iff.mpr hzero)
  apply DirectRunBlocks.not_connected L D (I \ D) hD hcompNe hdis hnull
  simpa only [union_sdiff_of_subset hproper.subset] using hconn

theorem exists_minimal (L : ℕ) (I D : Finset ℕ) (hproper : D ⊂ I) (hD : D.Nonempty)
    (hconn : ConnectedWindowFamilies.Connected L I) :
    ∃ A ⊆ I \ D, A.Nonempty ∧
      span (fun x ↦ squareClassSpace x L) D ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
      ∀ B : Finset ℕ, B ⊂ A →
        Disjoint (span (fun x ↦ squareClassSpace x L) D) (span (fun x ↦ squareClassSpace x L) B) :=
  MinimalSpanCrossing.exists_minimal _ _ _ (cut L I D hproper hD hconn)

end PaperP1.ConnectedSpanCrossing
