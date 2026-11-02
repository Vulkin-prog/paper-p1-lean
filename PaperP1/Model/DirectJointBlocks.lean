module

public import PaperP1.Model.DirectRunBlocks
public import PaperP1.Model.UnrestrictedRunComponents

/-! # Original joint activations factor across two independent effective block spaces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectJointBlocks

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.SubspaceFamilyRank

theorem factor (L : ℕ) (hL : 0 < L) (e f : Finset ℕ) (he : e.Nonempty) (hf : f.Nonempty)
    (hef : Disjoint e f)
    (hspaces : Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) f)) :
    infiniteJointMoment L (e ∪ f) = infiniteJointMoment L e * infiniteJointMoment L f := by
  have hnull := (DirectRunBlocks.additive_iff_spaces L e f hef).mpr hspaces
  obtain ⟨P, C, D, hP, hparts, hCD, hCe, hDf⟩ := DirectRunBlocks.exists_partition L e f he hf hef hnull
  calc
    _ = ∏ E ∈ P.parts, infiniteJointMoment L (FinitePartImage.image E) :=
      UnrestrictedRunComponents.joint_partition L hL (e ∪ f) P hP
    _ = _ := by rw [hparts, prod_pair hCD, hCe, hDf]

end PaperP1.DirectJointBlocks
