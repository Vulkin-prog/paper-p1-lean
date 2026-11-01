module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Model.CompatibleWindowPrescriptions
public import PaperP1.Model.CanonicalRunComponents

/-! # Prescribed tuple masses specialize to the original infinite run moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedRunMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance prescribedRunMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance prescribedRunMassMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem joint_eq_infinite {s L : ℕ} (x : Fin s → ℕ) (hL : 0 < L) :
    PrescribedTupleMass.joint L (fun _ ↦ startRhs L) x = infiniteFamilyJointMoment L x := by
  let M := (univ.sup x) + L
  have hcut : ∀ i, x i + L ≤ M := by
    intro i
    exact Nat.add_le_add_right (le_sup (f := x) (mem_univ i)) L
  rw [PrescribedTupleMass.joint, CompatibleWindowPrescriptions.source_mass_affine x (fun _ ↦ startRhs L) hcut,
    infiniteFamilyJointMoment_eq_finite M L x hcut, startFamilyJointMoment_eq_affineMass M L x hL]
  rfl

end PaperP1.PrescribedRunMass
