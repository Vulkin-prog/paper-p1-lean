module

public import PaperP1.Combinatorics.SmallFinpartition
public import PaperP1.Affine.DirectPartitions

/-! # At order three every full-support relation lies in one canonical direct component -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleFullSupportConnected

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]

theorem no_singleton_part (S : ι → Submodule 𝔽₂ U) (s : (i : ι) → S i)
    (hs : IsFullSupportRelation S s) (P : Finpartition (univ : Finset ι))
    (hP : RelationDirectPartition S P) : ∀ C ∈ P.parts, C.card ≠ 1 := by
  intro C hC hcard
  obtain ⟨i, rfl⟩ := card_eq_one.mp hcard
  have hzero := hP s hs.2 {i} hC
  rw [sum_singleton] at hzero
  exact hs.1 i (Subtype.ext hzero)

theorem connected (S : ι → Submodule 𝔽₂ U) (hcard : Fintype.card ι = 3)
    (s : (i : ι) → S i) (hs : IsFullSupportRelation S s) : canonicalRelationPartition S = ⊤ := by
  have huniv : (univ : Finset ι).card = 3 := by simpa only [card_univ] using hcard
  apply SmallFinpartition.eq_top_without_singletons
  · exact card_pos.mp (by omega : 0 < (univ : Finset ι).card)
  · omega
  · exact no_singleton_part S s hs _ (canonicalRelationPartition_respects S)

end PaperP1.TripleFullSupportConnected
