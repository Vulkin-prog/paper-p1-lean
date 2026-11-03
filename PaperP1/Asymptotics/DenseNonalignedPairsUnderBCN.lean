module

public import PaperP1.Asymptotics.DensePhysicalKernelWitnessUnderBCN
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization
public import PaperP1.Arithmetic.TwoTargetEmptySource

/-! # Dense nonaligned actual pairs have a subpower number of hosts

The sole unproved input in this route is the explicitly recorded BCN property.
Both actual marginal windows may have local rank defects.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseNonalignedPairsUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂)
      (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)
local instance codeAddCommGroup {L : ℕ} (X : Fin 0 ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂)
      (M := ((Fin 0 ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {L : ℕ} (X : Fin 0 ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P

theorem uniform_kernel_hosts (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L ⊥) : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, ht, hreg⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace 0 η hη
  let K : ℝ := PhysicalLabelSupportCount.supportBound 1 t (t - 1)
  let τ := ε / (16 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (16 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 4 * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := DensePhysicalKernelWitnessUnderBCN.uniform_witness
    c κ hc hBCN C τ (η / 2) hτ (by positivity) 1 t (by omega) (by omega) ht
  obtain ⟨NC, hcount⟩ := SmallKernelWindows.critical_two_count 1 C (ε / 4) (by norm_num) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max NW (max NC NG)), by omega, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T ×ˢ T := by
    intro p hp
    let x : Fin 0 → ℕ := Fin.elim0
    obtain ⟨M, hrec, hdim, hinj⟩ := hreg x p.1 p.2 L hL ⊥ bot_le disjoint_bot_left disjoint_bot_left
    have hX : ∀ i, starts x p.1 p.2 i ∈ dyadicBlock N := by
      rintro (i | j)
      · exact Fin.elim0 i
      · fin_cases j
        · simpa [starts] using (hdyadic p hp).1
        · simpa [starts] using (hdyadic p hp).2
    have hxy := ActualOffsetNonalignment.of_nonaligned hL
      (by have hh := (mem_Ico.mp (hdyadic p hp).1).1; omega)
      (by have hh := (mem_Ico.mp (hdyadic p hp).2).1; omega) (hnon p hp)
    have hno : ∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact
        (starts x p.1 p.2 i) (starts x p.1 p.2 j) L := by
      rintro (i | i) (j | j) hij
      · exact Fin.elim0 i
      · exact Fin.elim0 i
      · exact Fin.elim0 j
      · fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · simpa [starts] using hxy
        · simpa [starts] using hxy.symm
        · exact False.elim (hij rfl)
    have hproj : ∀ i, Function.Injective ((projection (starts x p.1 p.2) L i).comp M.subtype) := by
      rintro (i | j)
      · exact Fin.elim0 i
      · exact hinj j
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hh := hdense p hp
      have hnonneg : 0 ≤ η * L := by positivity
      linarith only [hh, hdim, hnonneg]
    have hsmall := hw N (by omega) L hband (Fin 0 ⊕ Fin 2) (by simp)
      (starts x p.1 p.2) hX hno M (L + 1) le_rfl hrec hproj hdim'
    apply mem_product.mpr
    constructor
    · simpa only [starts, ite_true, Fin.isValue] using hsmall (Sum.inr 0)
    · simpa only [starts, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hsmall (Sum.inr 1)
  have hT := hcount N (by omega) L (L + 1) (2 * τ * K) hband (by simp)
  have hfinite : (F.card : ℝ) ≤ (T.card : ℝ) * T.card := by
    exact_mod_cast ((card_le_card hsub).trans_eq (card_product T T))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ (T.card : ℝ) * T.card := hfinite
    _ ≤ (N : ℝ) ^ (2 * τ * K + ε / 4) * (N : ℝ) ^ (2 * τ * K + ε / 4) :=
      mul_le_mul hT hT (by positivity) (by positivity)
    _ = (N : ℝ) ^ (4 * τ * K + ε / 2) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hbudget

theorem companion_T8_3 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_kernel_hosts c κ hc hBCN C η ε hη hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  apply h N hN L hband F hdyadic hnon
  intro p hp
  rw [TwoTargetEmptySource.dimension]
  have hh := hdense p hp
  push_cast at hh
  linarith only [hh, hη]

end PaperP1.DenseNonalignedPairsUnderBCN
