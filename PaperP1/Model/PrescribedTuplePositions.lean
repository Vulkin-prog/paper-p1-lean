module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Combinatorics.TuplePositions
public import PaperP1.Model.JointBranchingEvents
public import PaperP1.Model.RunSeparation

/-! # Reindexing actual tuple masses and eliminating strictly overlapping run starts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedTuplePositions

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PrescribedTupleMass
  PaperP1.WindowFamilyConditional PaperP1.RelativeSignIndependence PaperP1.Model.InfiniteRademacher

local instance prescribedTuplePositionsMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem joint_permute {r L : ℕ} (c : ℕ → Fin L → F₂) (e : Equiv.Perm (Fin r)) (x : Fin r → ℕ) :
    joint L c (TuplePositions.permute e x) = joint L c x := by
  unfold joint
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sourceEvent, TuplePositions.permute, Function.comp_apply]
  constructor
  · intro h i
    simpa only [Equiv.apply_symm_apply] using h (e.symm i)
  · intro h i
    exact h (e i)

theorem run_joint_zero_of_close {r L : ℕ} (x : Fin r → ℕ) (hL : 0 < L)
    (i j : Fin r) (hij : x i < x j) (hclose : x j < x i + L) :
    joint L (fun _ ↦ startRhs L) x = 0 := by
  have hempty : {ω | sourceEvent x L (fun _ ↦ startRhs L) ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hω
    have hi := (JointBranchingEvents.startBits_eq_rhs_iff (x i) hL ω).mp (hω i)
    have hj := (JointBranchingEvents.startBits_eq_rhs_iff (x j) hL ω).mp (hω j)
    have hsep := RunSeparation.startEvent_separated _ hi hj hij
    omega
  rw [joint, hempty, measureReal_empty]

theorem positive_run_separation {r L : ℕ} (x : Fin r → ℕ) (hL : 0 < L)
    (hpos : 0 < joint L (fun _ ↦ startRhs L) x) (i j : Fin r) (hij : x i < x j) :
    x i + L ≤ x j := by
  by_contra hnot
  have hz := run_joint_zero_of_close x hL i j hij (by omega)
  rw [hz] at hpos
  exact lt_irrefl _ hpos

end PaperP1.PrescribedTuplePositions
