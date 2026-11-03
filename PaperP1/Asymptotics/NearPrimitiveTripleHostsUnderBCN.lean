module

public import PaperP1.Asymptotics.NearPrimitivePhysicalRegularization
public import PaperP1.Asymptotics.DensePhysicalKernelWitnessUnderBCN
public import PaperP1.Asymptotics.SmallKernelWindows
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Actual dense triples with weak proper intersections have a subpower host count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NearPrimitiveTripleHostsUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.Model PaperP1.Model.InfiniteStarts

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup (I : Finset ℕ) (L : ℕ) : AddCommGroup (code (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := ((I × Fin (L + 1)) → F₂)) (code (fun i : I ↦ i.val) L)
local instance physicalAddCommGroup (I : Finset ℕ) (L : ℕ)
    (M : Submodule F₂ (code (fun i : I ↦ i.val) L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code (fun i : I ↦ i.val) L) M

theorem uniform_hosts (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η θ ε : ℝ) (hη : 0 < η) (hθ : 0 ≤ θ) (hθsmall : θ < η / 100) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧
        η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ) ∧
        ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
          (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, ht, NR, _hNR, hreg⟩ := NearPrimitivePhysicalRegularization.uniform_subspace C η θ hη hθ hθsmall
  let K : ℝ := PhysicalLabelSupportCount.supportBound 2 t (t - 1)
  let τ := ε / (24 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (24 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 6 * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := DensePhysicalKernelWitnessUnderBCN.uniform_witness_active
    c κ hc hBCN C τ (η / 4) hτ (by positivity) 2 t (by omega) (by omega) ht
  obtain ⟨NC, hcount⟩ := SmallKernelWindows.critical_two_count 1 C (ε / 6) (by norm_num) (by positivity)
  refine ⟨3 + NR + NW + NC, by omega, ?_⟩
  intro N hN L hband F hF
  classical
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T.powersetCard 3 := by
    intro I hI
    obtain ⟨hcard, hdyadic, hdense, hweak⟩ := hF I hI
    let X : I → ℕ := fun i ↦ i.val
    have hι : Fintype.card I ≤ 3 := by simp only [Fintype.card_coe, hcard, le_refl]
    obtain ⟨M, hrec, hdim, hinj, hno⟩ := hreg N (by omega) L hband I hcard hdyadic hdense hweak
    have hX (i : I) : X i ∈ dyadicBlock N := hdyadic i.property
    have hsmall := hw N (by omega) L hband I hι X hX M (L + 1) le_rfl hno hrec hinj hdim
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

end PaperP1.NearPrimitiveTripleHostsUnderBCN
