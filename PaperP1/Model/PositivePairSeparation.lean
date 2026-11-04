module

public import PaperP1.Model.PrescribedTuplePositions
public import PaperP1.Model.JointTupleSupport

/-! # Positive actual pair probability forces literal run-start separation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositivePairSeparation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem of_joint {x y L : ℕ} (hL : 0 < L) (hxy : x < y)
    (hq : 0 < infiniteJointMoment L {x, y}) : x + L ≤ y := by
  let v : Fin 2 → ℕ := ![x, y]
  have hs : FiniteFamilyEnumeration.tupleSet v = {x, y} := by
    simp [FiniteFamilyEnumeration.tupleSet, v, univ_fin2]
  have heq : PrescribedTupleMass.joint L (fun _ ↦ startRhs L) v = infiniteJointMoment L {x, y} := by
    rw [JointTupleSupport.prescribed_eq_support v hL, hs]
  exact PrescribedTuplePositions.positive_run_separation v hL (by rwa [heq]) 0 1 hxy

end PaperP1.PositivePairSeparation
