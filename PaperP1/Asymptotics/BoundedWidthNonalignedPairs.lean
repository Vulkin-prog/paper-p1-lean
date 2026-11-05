module

public import PaperP1.Asymptotics.BoundedWidthPhysicalKernelWitness
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization
public import PaperP1.Arithmetic.TwoTargetEmptySource

/-! # Dense nonaligned comparable windows of any fixed logarithmic width have subpower many hosts

The original critical length stays separate from the physical window width.
Only actual intersections and exact offset nonalignment are used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedWidthNonalignedPairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z J : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z J W) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂)
      (M := W × squareClassSpace y J × squareClassSpace z J) (Kernel y z J W)
local instance codeAddCommGroup {J : ℕ} (X : Fin 0 ⊕ Fin 2 → ℕ) : AddCommGroup (code X J) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂)
      (M := ((Fin 0 ⊕ Fin 2) × Fin (J + 1)) → F₂) (code X J)
local instance physicalAddCommGroup {J : ℕ} (X : Fin 0 ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X J)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X J) P

theorem uniform_kernel_hosts_of_no_exact
    (A D : ℕ) (hA : 1 ≤ A) (hD : 1 ≤ D) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ J : ℕ, 1 ≤ J → J ≤ D * (L + 1) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, (N ≤ A * p.1 ∧ p.1 ≤ A * N) ∧ (N ≤ A * p.2 ∧ p.2 ≤ A * N)) →
      (∀ p ∈ F, ActualOffsetNonalignment.NoExact p.1 p.2 J) →
      (∀ p ∈ F, η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 J ⊥) : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hAr : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  let ξ : ℝ := η / D
  have hξ : 0 < ξ := div_pos hη hDr
  obtain ⟨t, ht, hreg⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace 0 ξ hξ
  let K : ℝ := PhysicalLabelSupportCount.supportBound 1 t (t - 1)
  let τ := ε / (16 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (16 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 4 * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := BoundedWidthPhysicalKernelWitness.uniform_witness
    A D hA C τ (η / 2) hτ (by positivity) 1 t (by omega) (by omega) ht
  obtain ⟨NC, hcount⟩ := TwoSmallKernelCount.critical_block_count (1 / (A : ℝ)) (A : ℝ)
    ((D + 1 : ℕ) : ℝ) ((D + 1 : ℕ) : ℝ) C (ε / 4)
    (by positivity) (by positivity) (by positivity) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max NW (max NC NG)), by omega, ?_⟩
  intro N hN L hband J hJ hJD F hcenters hnon hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by have hh := hgeom.2.2.1; omega
  have hJbound : J + 1 ≤ (D + 1) * (L + 1) := by nlinarith only [hJD, Nat.zero_le L]
  have hJtwo : (J : ℝ) ≤ 2 * (D : ℝ) * L := by
    have hLL : L + 1 ≤ 2 * L := by omega
    have hh : J ≤ 2 * D * L := by nlinarith only [hJD.trans (Nat.mul_le_mul_left D hLL)]
    exact_mod_cast hh
  have hcost : ξ * J / 4 ≤ η * L / 2 := by
    have hh := mul_le_mul_of_nonneg_left hJtwo hξ.le
    have he : ξ * (2 * (D : ℝ) * L) = 2 * η * L := by dsimp [ξ]; field_simp
    rw [he] at hh
    linarith only [hh]
  let T := (Icc 0 (A * N)).filter fun n ↦ N ≤ A * n ∧
    TwoSmallKernelCount.HasPair (J + 1) (J + 1) n ((N : ℝ) ^ (2 * τ * K))
  have hsub : F ⊆ T ×ˢ T := by
    intro p hp
    let x : Fin 0 → ℕ := Fin.elim0
    obtain ⟨M, hrec, hdim, hinj⟩ := hreg x p.1 p.2 J hJ ⊥ bot_le disjoint_bot_left disjoint_bot_left
    have hX : ∀ i, N ≤ A * starts x p.1 p.2 i ∧ starts x p.1 p.2 i ≤ A * N := by
      rintro (i | j)
      · exact Fin.elim0 i
      · fin_cases j
        · simpa [starts] using (hcenters p hp).1
        · simpa [starts] using (hcenters p hp).2
    have hxy := hnon p hp
    have hno : ∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact
        (starts x p.1 p.2 i) (starts x p.1 p.2 j) J := by
      rintro (i | i) (j | j) hij
      · exact Fin.elim0 i
      · exact Fin.elim0 i
      · exact Fin.elim0 j
      · fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · simpa [starts] using hxy
        · simpa [starts] using hxy.symm
        · exact False.elim (hij rfl)
    have hproj : ∀ i, Function.Injective ((projection (starts x p.1 p.2) J i).comp M.subtype) := by
      rintro (i | j)
      · exact Fin.elim0 i
      · exact hinj j
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hh := hdense p hp
      have hnonneg : 0 ≤ η * L := by positivity
      linarith only [hh, hdim, hnonneg, hcost]
    have hTin (j : Fin 2) : starts x p.1 p.2 (Sum.inr j) ∈ T := by
      have hc := hX (Sum.inr j)
      have hsmall := hw N (by omega) L hband J hJ hJD (Fin 0 ⊕ Fin 2) (by simp)
        (starts x p.1 p.2) hX M (J + 1) le_rfl
        (OffsetNonalignmentOn.of_global _ _ _ hno) hrec hdim' (Sum.inr j) (hinj j)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, hc.2⟩, hc.1, hsmall⟩
    apply mem_product.mpr
    constructor
    · simpa only [starts, ite_true, Fin.isValue] using hTin 0
    · simpa only [starts, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hTin 1
  have hT : (T.card : ℝ) ≤ (N : ℝ) ^ (2 * τ * K + ε / 4) := by
    apply (hcount N (by omega) L (J + 1) (J + 1) (2 * τ * K) hband
      (by exact_mod_cast hJbound) (by omega) (by exact_mod_cast hJbound) T ?_).2
    intro n hnT
    obtain ⟨hbox, hlow, hpair⟩ := mem_filter.mp hnT
    refine ⟨?_, by exact_mod_cast (mem_Icc.mp hbox).2, hpair⟩
    have hlo : (N : ℝ) ≤ (A : ℝ) * n := by exact_mod_cast hlow
    have hh : (N : ℝ) / (A : ℝ) ≤ n := (div_le_iff₀ hAr).mpr
      (by nlinarith only [hlo])
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hh
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

/-- The actual intersection formulation keeps arbitrary local rank defects. -/
theorem uniform_intersection_hosts
    (A D : ℕ) (hA : 1 ≤ A) (hD : 1 ≤ D) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ J : ℕ, 1 ≤ J → J ≤ D * (L + 1) →
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, (N ≤ A * p.1 ∧ p.1 ≤ A * N) ∧ (N ≤ A * p.2 ∧ p.2 ≤ A * N)) →
      (∀ p ∈ F, ActualOffsetNonalignment.NoExact p.1 p.2 J) →
      (∀ p ∈ F, η * L ≤ (Module.finrank F₂
        ↥(squareClassSpace p.1 J ⊓ squareClassSpace p.2 J) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_kernel_hosts_of_no_exact A D hA hD C η ε hη hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband J hJ hJD F hcenters hnon hdense
  apply h N hN L hband J hJ hJD F hcenters hnon
  intro p hp
  rw [TwoTargetEmptySource.dimension]
  exact hdense p hp

end PaperP1.BoundedWidthNonalignedPairs
