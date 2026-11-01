module

public import PaperP1.Model.SquareClassRelations
public import PaperP1.Affine.CanonicalCoefficientTransport

/-! # The canonical square-class and original run-character partitions coincide -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalSquareClasses

open PaperP1.Arithmetic PaperP1.Model PaperP1.Affine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem canonical_eq_rows (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M) :
    canonicalRelationPartition (squareClassFamilySpace L g) =
      canonicalRelationPartition (startFamilySpace M L g) := by
  apply CanonicalCoefficientTransport.canonical_eq _ _ (fun i ↦ squareClassEquivRow (hcut i))
  intro s
  exact (squareClassFamily_relation_zero_iff M L g hcut s).symm

theorem connected_iff_rows (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M) :
    canonicalRelationPartition (squareClassFamilySpace L g) = ⊤ ↔
      canonicalRelationPartition (startFamilySpace M L g) = ⊤ := by
  rw [canonical_eq_rows M L g hcut]

end PaperP1.CanonicalSquareClasses
