module

public import PaperP1.Asymptotics.DensePhysicalKernelWitnessUnderBCN
public import PaperP1.Asymptotics.CriticalTwoPointClasses
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.InjectivePhysicalRelationRegularization
public import PaperP1.Arithmetic.PrimitiveTrueWindowRelations
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Dense primitive true-window triples have a subpower number of hosts

The threshold is uniform over all actual primitive triple families.
Only the previously recorded explicit BCN property is unproved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveTripleHostsUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ConnectedWindowFamilies PaperP1.Model PaperP1.Model.InfiniteStarts

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance effectiveAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) :
    AddCommGroup (EffectiveKernel X L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : ι) → squareClassSpace (X i) L) (EffectiveKernel X L)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

theorem uniform_hosts (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, ht, hreg⟩ := InjectivePhysicalRelationRegularization.uniform_subspace η hη
  let K : ℝ := PhysicalLabelSupportCount.supportBound 2 t (t - 1)
  let τ := ε / (24 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (24 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 6 * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := DensePhysicalKernelWitnessUnderBCN.uniform_witness
    c κ hc hBCN C τ (η / 2) hτ (by positivity) 2 t (by omega) (by omega) ht
  obtain ⟨NC, hcount⟩ := SmallKernelWindows.critical_two_count 1 C (ε / 6) (by norm_num) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := CriticalTwoPointClasses.uniform_disjoint_no_exact C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max NW (max NC (max NR NG))), by omega, ?_⟩
  intro N hN L hband F hF
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T.powersetCard 3 := by
    intro I hI
    obtain ⟨hcard, hdyadic, hprim, hdense⟩ := hF I hI
    let X : I → ℕ := fun i ↦ i.val
    have hι : Fintype.card I ≤ 3 := by simp only [Fintype.card_coe, hcard, le_refl]
    obtain ⟨M, hrec, hdim, hinj⟩ := hreg I hι X L hL
      (PrimitiveTrueWindowRelations.projection_injective I L hprim)
    have hX (i : I) : X i ∈ dyadicBlock N := hdyadic i.property
    have hno : ∀ i j : I, i ≠ j → ActualOffsetNonalignment.NoExact (X i) (X j) L := by
      intro i j hij
      exact hr N (by omega) L hband (X i) (X j)
        (mem_Ico.mp (hX i)).1 (mem_Ico.mp (hX j)).1
        (PrimitiveTrueWindowRelations.pair_disjoint I L (by omega) hprim i j hij)
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hdimR : Module.finrank F₂ (EffectiveKernel X L) = runRelativeNullity L I :=
        PrimitiveTrueWindowRelations.dimension I L
      rw [hdimR] at hdim
      have hnonneg : 0 ≤ η * L := by positivity
      linarith only [hdense, hdim, hnonneg]
    have hsmall := hw N (by omega) L hband I hι X hX hno M (L + 1) le_rfl hrec hinj hdim'
    exact mem_powersetCard.mpr ⟨fun x hx ↦ hsmall ⟨x, hx⟩, hcard⟩
  have hfinite : (F.card : ℝ) ≤ (T.card : ℝ) ^ 3 := by
    have hh := (card_le_card hsub).trans_eq (card_powersetCard 3 T)
    exact_mod_cast hh.trans (Nat.choose_le_pow T.card 3)
  have hT := hcount N (by omega) L (L + 1) (2 * τ * K) hband (by simp)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ (T.card : ℝ) ^ 3 := hfinite
    _ ≤ ((N : ℝ) ^ (2 * τ * K + ε / 6)) ^ 3 := pow_le_pow_left₀ (by positivity) hT 3
    _ = (N : ℝ) ^ (6 * τ * K + ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hbudget

theorem companion_T8_2_hosts (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_hosts c κ hc hBCN C η ε hη hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  apply h N hN L hband F
  intro I hI
  obtain ⟨hcard, hdyadic, hprim, hdense⟩ := hF I hI
  refine ⟨hcard, hdyadic, hprim, ?_⟩
  push_cast at hdense
  linarith only [hdense, hη]

end PaperP1.DensePrimitiveTripleHostsUnderBCN
