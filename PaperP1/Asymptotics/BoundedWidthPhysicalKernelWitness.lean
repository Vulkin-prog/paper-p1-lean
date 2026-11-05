module

public import PaperP1.Asymptotics.BoundedWidthPhysicalGroupCount
public import PaperP1.Asymptotics.TwoSmallKernelCount
public import PaperP1.Arithmetic.ActiveGroupKernelErasureAt
public import PaperP1.Arithmetic.SmallKernelWindowSets

/-! # Two small kernels in any comparable block of bounded logarithmic width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedWidthPhysicalKernelWitness

universe u

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups PaperP1.LargeOddKernel PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (J : ℕ) : AddCommGroup (code X J) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (J + 1)) → F₂)) (code X J)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (J : ℕ)
    (M : Submodule F₂ (code X J)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X J) M

theorem uniform_witness
    (A D : ℕ) (hA : 1 ≤ A) (C τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) (d t : ℕ) (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ J : ℕ, 1 ≤ J → J ≤ D * (L + 1) →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ d + 1 →
      ∀ X : ι → ℕ, (∀ i, N ≤ A * X i ∧ X i ≤ A * N) →
      ∀ (M : Submodule F₂ (code X J)) (H : ℕ), J + 1 ≤ H →
      OffsetNonalignmentOn.NoExactOn X J (fun v ↦ label X J M v ≠ 0) →
      DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X J)) M d t →
      η * L ≤ (Module.finrank F₂ M : ℝ) →
      ∀ i : ι, Function.Injective ((projection X J i).comp M.subtype) → TwoSmallKernelCount.HasPair H (J + 1) (X i)
        ((N : ℝ) ^ (2 * τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ))) := by
  obtain ⟨NG, _hNG, hg⟩ := BoundedWidthPhysicalGroupCount.uniform_count_active
    A D hA C τ (η / 24) hτ (by positivity)
  obtain ⟨NW, hw⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NG NW), by omega, ?_⟩
  intro N hN L hband J hJ hJD ι _ _ hι X hX M H hH hno hrec hdim i hinj
  have hgeom := hw N (by omega) L hband
  have hL : 1 ≤ L := by have hh := hgeom.2.2.1; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hXpos (j : ι) : 1 ≤ X j := by
    have hh := (hX j).1
    by_contra hn
    have hz : X j = 0 := by omega
    rw [hz, Nat.mul_zero] at hh
    omega
  have hcount := hg N (by omega) L hband J hJD ι (by omega) X hX M H hH hno
  have hlarge : 3 * (largeGroups X J M H ((N : ℝ) ^ τ)).card < Module.finrank F₂ M := by
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hpositive : 0 < η * L := mul_pos hη (by linarith)
    have hc : 3 * ((largeGroups X J M H ((N : ℝ) ^ τ)).card : ℝ) < Module.finrank F₂ M := by
      push_cast at hcount
      nlinarith only [hcount, hdim, hLR, hpositive, mul_pos hη (by norm_num : (0 : ℝ) < 1)]
    exact_mod_cast hc
  obtain ⟨a, b, hab, ha, hb⟩ := ActiveGroupKernelErasureAt.two_small X J M H d t
    hXpos hH hι hd hd₂ ht hrec i hinj ((N : ℝ) ^ τ) (Real.one_le_rpow hN1 hτ.le) hlarge
  have hcap : ((N : ℝ) ^ τ) ^ PhysicalLabelSupportCount.supportBound d t (t - 1) =
      (N : ℝ) ^ (τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
  rw [hcap] at ha hb
  have hi : 0 < X i := by have hh := hXpos i; omega
  have hoff (v : Fin (J + 1)) : (NormalizedUnitCount.offset v).natAbs ≤ J + 1 := by
    have hh := EnlargedPairGeometry.offset_abs v
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  have hvalue (v : Fin (J + 1)) :
      LinearKernelFibres.value (X i) (NormalizedUnitCount.offset v) =
        startCompleteVertexLabel (X i) J v := by
    unfold LinearKernelFibres.value
    rw [← NormalizedUnitCount.label_cast hi v]
    exact Int.natAbs_natCast _
  refine ⟨NormalizedUnitCount.offset a, NormalizedUnitCount.offset b, hoff a, hoff b,
    (NormalizedUnitCount.offset_injective J).ne hab, ?_⟩
  have hprod := mul_le_mul ha hb (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)] at hprod
  have he : τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ) +
      τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ) =
      2 * τ * (PhysicalLabelSupportCount.supportBound d t (t - 1) : ℝ) := by ring
  rw [he] at hprod
  simpa only [TwoSmallKernelFibres.largeKernel, hvalue, Nat.cast_mul,
    WindowPrimeIncidence.value] using hprod

end PaperP1.BoundedWidthPhysicalKernelWitness
