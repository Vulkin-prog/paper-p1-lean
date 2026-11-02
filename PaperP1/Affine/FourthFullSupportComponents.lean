module

public import PaperP1.Combinatorics.FourFinpartition
public import PaperP1.Affine.TripleFullSupportConnected

/-! # Full-support relations at order four have one component or two pair components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthFullSupportComponents

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]

theorem connected_or_two_pairs (S : ι → Submodule 𝔽₂ U) (hcard : Fintype.card ι = 4)
    (s : (i : ι) → S i) (hs : IsFullSupportRelation S s) :
    canonicalRelationPartition S = ⊤ ∨ ∃ C D : Finset ι, C ≠ D ∧
      (canonicalRelationPartition S).parts = {C, D} ∧ C.card = 2 ∧ D.card = 2 := by
  apply FourFinpartition.top_or_two_pairs
  · simpa only [card_univ] using hcard
  · exact TripleFullSupportConnected.no_singleton_part S s hs _ (canonicalRelationPartition_respects S)

end PaperP1.FourthFullSupportComponents
