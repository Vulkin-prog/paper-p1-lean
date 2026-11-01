module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Model.CompatibleWindowPrescriptions
public import PaperP1.Model.SquareClassRelations

/-! # Actual prescribed tuple mass and its total effective square-class rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedTupleRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance prescribedTupleRankTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance prescribedTupleRankMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem total_rank_eq_rows {s M L : ℕ} (x : Fin s → ℕ) (hcut : ∀ i, x i + L ≤ M) :
    Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) =
      Module.finrank F₂ (⨆ i, startFamilySpace M L x i : Submodule F₂ (SampleSpace M →ₗ[F₂] F₂)) := by
  have hs := relativeNullity_dimension_identity (squareClassFamilySpace L x)
  have hr := relativeNullity_dimension_identity (startFamilySpace M L x)
  have hnullity := relativeNullity_squareClassFamily_eq_rows M L x hcut
  have hlocal : (∑ i, Module.finrank F₂ (squareClassFamilySpace L x i)) =
      ∑ i, Module.finrank F₂ (startFamilySpace M L x i) := by
    apply sum_congr rfl
    intro i _
    exact finrank_squareClassSpace_eq_effectiveRows (hcut i)
  have heq : Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) +
      relativeNullity (startFamilySpace M L x) =
      Module.finrank F₂ (⨆ i, startFamilySpace M L x i : Submodule F₂ (SampleSpace M →ₗ[F₂] F₂)) +
      relativeNullity (startFamilySpace M L x) := by
    calc
      _ = ∑ i, Module.finrank F₂ (squareClassFamilySpace L x i) := by
        simpa only [squareClassFamilySpace, hnullity] using hs.symm
      _ = ∑ i, Module.finrank F₂ (startFamilySpace M L x i) := hlocal
      _ = _ := hr
  exact Nat.add_right_cancel heq

theorem joint_zero_or_rank {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) :
    PrescribedTupleMass.joint L c x = 0 ∨ PrescribedTupleMass.joint L c x =
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  let M := (univ.sup x) + L
  have hcut : ∀ i, x i + L ≤ M := fun i ↦ Nat.add_le_add_right (le_sup (f := x) (mem_univ i)) L
  have hmass := CompatibleWindowPrescriptions.source_mass_affine x (fun i ↦ c (x i)) hcut
  change PrescribedTupleMass.joint L c x = _ at hmass
  by_cases hc : Compatible (familyStartSystem M L x) (fun p ↦ c (x p.1) p.2)
  · right
    rw [hmass, compatible_mass_eq_effectiveRate _ _ hc, effectiveRate,
      card_eq_two_pow_finrank (V := effectiveRowSpace (familyStartSystem M L x))]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [effectiveRowSpace_familyStartSystem, ← total_rank_eq_rows x hcut]
  · left
    rw [hmass]
    exact uniformSolutionMass_of_not_compatible _ _ hc

theorem joint_le_rank {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) :
    PrescribedTupleMass.joint L c x ≤
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (x i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  rcases joint_zero_or_rank c x with hz | hq
  · rw [hz]; positivity
  · exact hq.le

end PaperP1.PrescribedTupleRank
