module

public import PaperP1.Model.RelativeWindowFamilies

/-! # Connected actual families participate at every coordinate, with a relation allowed to depend on that coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedParticipatingWindows

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ConnectedWindowFamilies

theorem witnesses (L : ℕ) (I : Finset ℕ) (hsize : 2 ≤ I.card)
    (hconn : Connected L I) : RelativeWindowFamilies.Witnesses L ⊥ I := by
  classical
  let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [Fintype.card_coe] using (show 1 < I.card by omega))
  intro i
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨u, hsum, hne⟩ := ConnectedRelations.coordinate_relation
    (fun x : I ↦ squareClassSpace x.val L) hconn i j (fun hij ↦ hji hij.symm)
  refine ⟨u, (fun hz ↦ hne (congrArg Subtype.val hz)), ?_⟩
  simpa only [relationAddition_apply, Submodule.mem_bot] using hsum

end PaperP1.ConnectedParticipatingWindows
