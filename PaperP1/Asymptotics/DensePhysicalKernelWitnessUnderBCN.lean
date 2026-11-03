module

public import PaperP1.Asymptotics.ActivePhysicalGroupCountUnderBCN
public import PaperP1.Arithmetic.ActiveGroupKernelErasure
public import PaperP1.Arithmetic.SmallKernelWindowSets

/-! # Dense regularized relations force two small kernels in every actual block -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePhysicalKernelWitnessUnderBCN

universe u

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups PaperP1.LargeOddKernel PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

theorem uniform_witness (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (d t : ℕ) (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ d + 1 →
      ∀ X : ι → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      (∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact (X i) (X j) L) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H →
      DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M d t →
      (∀ i, Function.Injective ((projection X L i).comp M.subtype)) →
      η * L ≤ (Module.finrank F₂ M : ℝ) →
      ∀ i : ι, X i ∈ SmallKernelWindowSets.twoWindows N L H
        (2 * τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ)) := by
  obtain ⟨NG, _hNG, hg⟩ := ActivePhysicalGroupCountUnderBCN.uniform_count
    c κ hc hBCN C τ (η / 24) hτ (by positivity)
  obtain ⟨NW, hw⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NG NW), by omega, ?_⟩
  intro N hN L hband ι _ _ hι X hX hno M H hH hrec hinj hdim i
  have hgeom := hw N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hXpos (j : ι) : 1 ≤ X j := by
    have hh := (mem_Ico.mp (hX j)).1
    omega
  have hcount := hg N (by omega) L hband ι (by omega) X hX hno M H hH
  have hlarge : 3 * (largeGroups X L M H ((N : ℝ) ^ τ)).card < Module.finrank F₂ M := by
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hpositive : 0 < η * L := mul_pos hη (by linarith)
    have hc : 3 * ((largeGroups X L M H ((N : ℝ) ^ τ)).card : ℝ) < Module.finrank F₂ M := by
      push_cast at hcount
      nlinarith only [hcount, hdim, hLR, hpositive, mul_pos hη (by norm_num : (0 : ℝ) < 1)]
    exact_mod_cast hc
  obtain ⟨a, b, hab, ha, hb⟩ := ActiveGroupKernelErasure.two_small_per_block X L M H d t
    hXpos hH hι hd hd₂ ht hrec hinj ((N : ℝ) ^ τ) (Real.one_le_rpow hN1 hτ.le) hlarge i
  have hcap : ((N : ℝ) ^ τ) ^ PhysicalLabelSupportCount.supportBound d t (t - 1) =
      (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
  rw [hcap] at ha hb
  have hi : 0 < X i := by have hh := hXpos i; omega
  apply mem_filter.mpr
  refine ⟨hX i, startCompleteVertexLabel (X i) L a, NormalizedWindowSets.mem_values.mpr ⟨a, rfl⟩,
    startCompleteVertexLabel (X i) L b, NormalizedWindowSets.mem_values.mpr ⟨b, rfl⟩,
    (fun he ↦ hab (startCompleteVertexLabel_injective hi he)), ?_⟩
  change ((largeOddKernel H (WindowPrimeIncidence.value X L (i, a)) *
    largeOddKernel H (WindowPrimeIncidence.value X L (i, b)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul]
  calc
    _ ≤ (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ)) *
        (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ)) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      congr 1
      ring

end PaperP1.DensePhysicalKernelWitnessUnderBCN
