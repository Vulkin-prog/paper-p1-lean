module

public import PaperP1.Asymptotics.DenseAnchoredKernelWitness
public import PaperP1.Affine.RelationKernelReindex
public import PaperP1.Combinatorics.PointedFiniteEnumeration
public import PaperP1.Asymptotics.CriticalTwoPointClasses
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.FixedArityPhysicalRelationRegularization
public import PaperP1.Arithmetic.PrimitiveTrueWindowRelations
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Dense primitive true-window families of any fixed size have a subpower number of hosts

The threshold is uniform over all actual primitive families of the prescribed size.
The bounded-degree confinement input is internally proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveHosts

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

theorem uniform_hosts
    (r : ℕ) (hr : 3 ≤ r) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = r ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  obtain ⟨t, ht, hreg⟩ := FixedArityPhysicalRelationRegularization.uniform_subspace
    (r - 1) (by omega) η hη
  let K : ℝ := PhysicalLabelSupportCount.supportBound (r - 1) t (t - 1)
  let τ := ε / (8 * r * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (8 * r * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 2 * r * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε, mul_nonneg hτ.le hrR.le]
  obtain ⟨NW, _hNW, hw⟩ := DenseAnchoredKernelWitness.uniform_witness
    (r - 1) (by omega) C τ (η / 2) hτ (by positivity) t ht
  obtain ⟨NC, hcount⟩ := SmallKernelWindows.critical_two_count 1 C (ε / (2 * r))
    (by norm_num) (by positivity)
  obtain ⟨NR, _hNR, hnoExact⟩ := CriticalTwoPointClasses.uniform_disjoint_no_exact C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max NW (max NC (max NR NG))), by omega, ?_⟩
  intro N hN L hband F hF
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T.powersetCard r := by
    intro I hI
    obtain ⟨hcard, hdyadic, hprim, hdense⟩ := hF I hI
    apply mem_powersetCard.mpr
    refine ⟨?_, hcard⟩
    intro x hx
    obtain ⟨e, he⟩ := PointedFiniteEnumeration.exists_equiv (r - 1)
      (ι := I) (by simp only [Fintype.card_coe, hcard]; omega) ⟨x, hx⟩
    let X : Option (Fin (r - 1)) → ℕ := fun i ↦ (e i).val
    have hι : Fintype.card (Option (Fin (r - 1))) ≤ r - 1 + 1 := by simp
    have hproj (j : Option (Fin (r - 1))) : Function.Injective (effectiveProjection X L j) :=
      RelationKernelReindex.projection_injective (fun i : I ↦ squareClassSpace i.val L) e j
        (PrimitiveTrueWindowRelations.projection_injective I L hprim (e j))
    obtain ⟨M, hrec, hdim, hinj⟩ := hreg (Option (Fin (r - 1))) hι X L hL hproj
    have hX (i : Option (Fin (r - 1))) : X i ∈ dyadicBlock N := hdyadic (e i).property
    have hno : OffsetNonalignmentFrom.NoExactFrom X L
        (fun v ↦ PrimeCircuitSupports.label X L M v ≠ 0) none := by
      apply OffsetNonalignmentFrom.of_global
      intro j hj
      exact hnoExact N (by omega) L hband (X none) (X j)
        (mem_Ico.mp (hX none)).1 (mem_Ico.mp (hX j)).1
        (PrimitiveTrueWindowRelations.pair_disjoint I L (by omega) hprim (e none) (e j)
          (fun hh ↦ hj (e.injective hh).symm))
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hdimR : Module.finrank F₂ (EffectiveKernel X L) = runRelativeNullity L I :=
        RelationKernelReindex.finrank_eq (fun i : I ↦ squareClassSpace i.val L) e
      rw [hdimR] at hdim
      have hnonneg : 0 ≤ η * L := by positivity
      linarith only [hdense, hdim, hnonneg]
    have hsmall := hw N (by omega) L hband X hX M (L + 1) le_rfl hno hrec hdim' (hinj none)
    have heval : X none = x := congrArg Subtype.val he
    simpa only [heval] using hsmall
  have hfinite : (F.card : ℝ) ≤ (T.card : ℝ) ^ r := by
    have hh := (card_le_card hsub).trans_eq (card_powersetCard r T)
    exact_mod_cast hh.trans (Nat.choose_le_pow T.card r)
  have hT := hcount N (by omega) L (L + 1) (2 * τ * K) hband (by simp)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ (T.card : ℝ) ^ r := hfinite
    _ ≤ ((N : ℝ) ^ (2 * τ * K + ε / (2 * r))) ^ r := pow_le_pow_left₀ (by positivity) hT r
    _ = (N : ℝ) ^ (2 * r * τ * K + ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      congr 1
      field_simp
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hbudget


end PaperP1.DensePrimitiveHosts
