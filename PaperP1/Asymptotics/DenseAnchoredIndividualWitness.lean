module

public import PaperP1.Asymptotics.DenseAnchoredKernelWitness
public import PaperP1.Arithmetic.SmallKernelWindowSets

/-! # Separate small-kernel bounds at an arbitrary physical anchor

The physical witness already constructs two individual bounds before multiplying
its two kernels. This interface exposes those bounds with one threshold uniform
in the window centres, physical relation space and cutoff. It retains active
nonalignment, disjoint-recovery exclusion and the injective anchor projection.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseAnchoredIndividualWitness

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.PrimeCircuitSupports PaperP1.AnchoredPhysicalPrimeGroups PaperP1.LargeOddKernel PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Option (Fin s) × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

theorem uniform_individual_witness (s : ℕ) (hs : 1 ≤ s)
    (C τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (t : ℕ) (ht : 2 ≤ t) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ X : Option (Fin s) → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H →
      OffsetNonalignmentFrom.NoExactFrom X L (fun v ↦ label X L M v ≠ 0) none →
      DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M s t →
      η * L ≤ (Module.finrank F₂ M : ℝ) →
      Function.Injective ((projection X L none).comp M.subtype) →
      ∃ a b : ℕ, a ∈ NormalizedWindowSets.values (X none) L ∧
        b ∈ NormalizedWindowSets.values (X none) L ∧ a ≠ b ∧
        ((largeOddKernel H a : ℕ) : ℝ) ≤
          (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) ∧
        ((largeOddKernel H b : ℕ) : ℝ) ≤
          (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) := by
  obtain ⟨NG, _hNG, hg⟩ := AnchoredPhysicalGroupCount.uniform_count_active s hs
    C τ (η / 8) hτ (by positivity)
  obtain ⟨NW, hw⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NG NW), by omega, ?_⟩
  intro N hN L hband X hX M H hH hno hrec hdim hinj
  have hgeom := hw N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hXpos (j : Option (Fin s)) : 1 ≤ X j := by
    have hh := (mem_Ico.mp (hX j)).1
    omega
  have hcount := hg N (by omega) L hband X hX M H hH hXpos hno
  have hlarge : (largeGroups X M H hXpos hH ((N : ℝ) ^ τ)).card < Module.finrank F₂ M := by
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hpositive : 0 < η * L := mul_pos hη (by linarith)
    have hc : ((largeGroups X M H hXpos hH ((N : ℝ) ^ τ)).card : ℝ) < Module.finrank F₂ M := by
      push_cast at hcount
      nlinarith only [hcount, hdim, hLR, hpositive, mul_pos hη (by norm_num : (0 : ℝ) < 1)]
    exact_mod_cast hc
  obtain ⟨a, b, hab, ha, hb⟩ := two_small X M hXpos hH t hs ht hrec hinj
    ((N : ℝ) ^ τ) (Real.one_le_rpow hN1 hτ.le) hlarge
  have hcap : ((N : ℝ) ^ τ) ^ PhysicalLabelSupportCount.supportBound s t (t - 1) =
      (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
  rw [hcap] at ha hb
  have hi : 0 < X none := by have hh := hXpos none; omega
  refine ⟨startCompleteVertexLabel (X none) L a,
    startCompleteVertexLabel (X none) L b,
    NormalizedWindowSets.mem_values.mpr ⟨a, rfl⟩,
    NormalizedWindowSets.mem_values.mpr ⟨b, rfl⟩,
    (fun he ↦ hab (startCompleteVertexLabel_injective hi he)), ?_, ?_⟩
  · exact ha
  · exact hb

end PaperP1.DenseAnchoredIndividualWitness
