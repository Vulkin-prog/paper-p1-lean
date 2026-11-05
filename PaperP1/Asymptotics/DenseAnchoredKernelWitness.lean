module

public import PaperP1.Asymptotics.AnchoredPhysicalGroupCount
public import PaperP1.Arithmetic.SmallKernelWindowSets

/-! # Dense anchored physical relations at every fixed arity give two small kernels

Only the anchor projection must be injective. Other windows may have dependent
projections or be aligned among themselves.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseAnchoredKernelWitness

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

theorem uniform_witness (s : ℕ) (hs : 1 ≤ s)
    (C τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (t : ℕ) (ht : 2 ≤ t) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ X : Option (Fin s) → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H →
      OffsetNonalignmentFrom.NoExactFrom X L (fun v ↦ label X L M v ≠ 0) none →
      DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M s t →
      η * L ≤ (Module.finrank F₂ M : ℝ) →
      Function.Injective ((projection X L none).comp M.subtype) →
      X none ∈ SmallKernelWindowSets.twoWindows N L H
        (2 * τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) := by
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
  apply mem_filter.mpr
  refine ⟨hX none, startCompleteVertexLabel (X none) L a, NormalizedWindowSets.mem_values.mpr ⟨a, rfl⟩,
    startCompleteVertexLabel (X none) L b, NormalizedWindowSets.mem_values.mpr ⟨b, rfl⟩,
    (fun he ↦ hab (startCompleteVertexLabel_injective hi he)), ?_⟩
  change ((largeOddKernel H (WindowPrimeIncidence.value X L (none, a)) *
    largeOddKernel H (WindowPrimeIncidence.value X L (none, b)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul]
  calc
    _ ≤ (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) *
        (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      congr 1
      ring

end PaperP1.DenseAnchoredKernelWitness
