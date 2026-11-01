module

public import PaperP1.Model.StartPartitionTransfer
public import PaperP1.Model.CanonicalRunComponents
public import PaperP1.Affine.CommonAffineWitness

/-! # Original run moments with a common, explicitly solving affine sample -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonRunMoments

open PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Affine

local instance commonRunMomentsTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem witness_event (M L : ℕ) (g : ι → ℕ) (σ : SampleSpace M)
    (hσ : ∀ i, startSystem M (g i) L σ = startRhs L) (i : ι) :
    effectiveEvent (startFamilySpace M L g i)
      (startFamilyWitness M L g (fun i ↦ ⟨σ, hσ i⟩) i) σ := by
  rw [effectiveRowEvent_iff]
  exact (hσ i).trans (affineWitness_solves _ _ (⟨σ, hσ i⟩)).symm

theorem joint_common (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (σ : SampleSpace M)
    (hσ : ∀ i, startSystem M (g i) L σ = startRhs L) :
    startFamilyJointMoment M L g = effectiveJointMoment (startFamilySpace M L g) (fun _ ↦ σ) := by
  rw [startFamilyJointMoment_eq_effective M L g hL (fun i ↦ ⟨σ, hσ i⟩)]
  exact effectiveJointMoment_common_witness _ _ σ (witness_event M L g σ hσ)

theorem centered_common (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (σ : SampleSpace M)
    (hσ : ∀ i, startSystem M (g i) L σ = startRhs L) :
    startFamilyCenteredMoment M L g = effectiveCenteredMoment (startFamilySpace M L g) (fun _ ↦ σ) := by
  rw [startFamilyCenteredMoment_eq_effective M L g hL (fun i ↦ ⟨σ, hσ i⟩)]
  exact effectiveCenteredMoment_common_witness _ _ σ (witness_event M L g σ hσ)

theorem infinite_joint_common (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (σ : SampleSpace M)
    (hσ : ∀ i, startSystem M (g i) L σ = startRhs L) :
    infiniteFamilyJointMoment L g = effectiveJointMoment (startFamilySpace M L g) (fun _ ↦ σ) := by
  rw [infiniteFamilyJointMoment_eq_finite M L g hcut]
  exact joint_common M L g hL σ hσ

theorem infinite_centered_common (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (σ : SampleSpace M)
    (hσ : ∀ i, startSystem M (g i) L σ = startRhs L) :
    infiniteFamilyCenteredMoment L g = effectiveCenteredMoment (startFamilySpace M L g) (fun _ ↦ σ) := by
  rw [infiniteFamilyCenteredMoment_eq_finite M L g hcut]
  exact centered_common M L g hL σ hσ

end PaperP1.CommonRunMoments
