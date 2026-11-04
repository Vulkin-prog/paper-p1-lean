module

public import PaperP1.Affine.OneSeedParticipation
public import PaperP1.Arithmetic.EvenWindowEnlargement
public import PaperP1.Model.RelativeWindowFamilies

/-! # Actual bounded old blocks inside common enlarged complete windows

Every actual target coordinate participates. A collision with the enlarged
source centre is retained by the proved insert-or-erase alternative.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneSeedWindowParticipation

open Finset PaperP1.Arithmetic PaperP1.Model

theorem insert_or_erase {L H a : ℕ} {I U : Finset ℕ}
    (hLH : L ≤ H) (hpos : ∀ x ∈ I, 0 < x)
    (hsource : FiniteEvenSquareClasses.space U ≤ squareClassSpace a H)
    (hw : RelativeWindowFamilies.Witnesses L (FiniteEvenSquareClasses.space U) I) :
    RelativeWindowFamilies.Witnesses H ⊥ (insert a I) ∨ RelativeWindowFamilies.Witnesses H ⊥ (I.erase a) := by
  have hh : OneSeedParticipation.Witnesses (fun x ↦ squareClassSpace x H)
      (squareClassSpace a H) I := OneSeedParticipation.mono
    (fun x ↦ squareClassSpace x L) (fun x ↦ squareClassSpace x H)
    (FiniteEvenSquareClasses.space U) (squareClassSpace a H) I
    (fun x hx ↦ EvenWindowEnlargement.window_mono (hpos x hx) hLH) hsource hw
  exact OneSeedParticipation.insert_or_erase (fun x ↦ squareClassSpace x H)
    (squareClassSpace a H) a I le_rfl hh

theorem bounded_block {L X R : ℕ} {I U : Finset ℕ} (hRX : R < X) (hLR : L ≤ 2 * R)
    (hpos : ∀ x ∈ I, 0 < x) (hU : ∀ n ∈ U, X - R ≤ n ∧ n ≤ X + R)
    (hw : RelativeWindowFamilies.Witnesses L (FiniteEvenSquareClasses.space U) I) :
    RelativeWindowFamilies.Witnesses (2 * R) ⊥ (insert (X - R + 1) I) ∨
      RelativeWindowFamilies.Witnesses (2 * R) ⊥ (I.erase (X - R + 1)) :=
  insert_or_erase hLR hpos (EvenWindowEnlargement.block_le_window hRX hU) hw

end PaperP1.OneSeedWindowParticipation
