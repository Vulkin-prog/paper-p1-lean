module

public import PaperP1.Asymptotics.DensePhysicalAnchorWitness
public import PaperP1.Asymptotics.AlignedSourcePool
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization
public import PaperP1.Arithmetic.PhysicalCoordinateErasureAt
public import PaperP1.Asymptotics.WeakAlignedActiveNonalignment
public import PaperP1.Asymptotics.WeakAlignmentUnitCount

/-! # Dense weakly aligned target pairs above any fixed source subspace have subpower hosts

A target is either in the deterministic aligned-source pool or has an actual
anchored small-kernel witness. Source windows may be mutually dependent and
the effective source subspace may be any subspace of their full value span.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTwoTargetWeakHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PhysicalWindowRelations PaperP1.TwoTargetWindowSections

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P

theorem uniform_hosts (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨_t₀, _ht₀, hreg⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace
    s (η / 4) (by positivity)
  obtain ⟨t, _ht, hwitness⟩ := DensePhysicalAnchorWitness.uniform_parameter (s + 1) (by omega)
    (η / 2) (by positivity)
  let K : ℝ := PhysicalLabelSupportCount.supportBound (s + 1) t (t - 1)
  let τ := ε / (32 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (32 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 4 * τ * K + ε / 4 ≤ ε / 2 := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := hwitness C τ hτ
  obtain ⟨NC, hc⟩ := SmallKernelWindows.critical_two_count 1 C (ε / 8) (by norm_num) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := AlignedSourcePool.uniform_count s 1 C (ε / 8) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (ε / 2) (ε / 2) (by positivity)
  obtain ⟨NU, _hNU, hu⟩ := WeakAlignmentUnitCount.uniform_weak_bound C
  obtain ⟨NZ, _hNZ, hzactive⟩ := WeakAlignedActiveNonalignment.uniform_no_exact C
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (32 / η)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨3 + NW + NC + NA + NF + NU + NZ + NG, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hweak hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hηL : (32 : ℝ) ≤ η * L := by
    have hprod := (div_lt_iff₀ hη).mp hL₀
    have hlength : (L₀ : ℝ) ≤ L := by exact_mod_cast (show L₀ ≤ L by omega)
    have hm := mul_le_mul_of_nonneg_left hlength hη.le
    nlinarith only [hprod, hm]
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  let A := AlignedSourcePool.pool (dyadicBlock N) x 1 L
  let U := T ∪ A
  have hsub : F ⊆ U ×ˢ U := by
    intro p hp
    let Y := starts x p.1 p.2
    obtain ⟨P₀, _hrec, hdim₀, hinj₀⟩ := hreg x p.1 p.2 L hL W hW (hdense p hp).1 (hdense p hp).2.1
    obtain ⟨a, b, ha₀, hb₀, _hcop, haH, hbH, hab⟩ := (hweak p hp).1
    have hgeomab : EnlargedPairGeometry.Geometric a b p.1 p.2 L := by
      simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hab
    let D := NormalizedUnitCount.units a b p.1 p.2 L
    let E := TwoTargetUnitExclusion.unitEndpoints (s := s) D
    have hDcard := hu N (by omega) L hband p.1 p.2 (hdyadic p hp).1 (hdyadic p hp).2
      (η / 64) (hweak p hp).2 a b ha₀ hb₀
    have hEcard : (E.card : ℝ) ≤ 2 * (η / 64) * L + 4 := by
      have hh : (E.card : ℝ) ≤ 2 * (D.card : ℝ) := by
        exact_mod_cast TwoTargetUnitExclusion.endpoints_card (s := s) D
      nlinarith only [hh, hDcard]
    obtain ⟨M, _hMP, hcost, hzero, hproj⟩ := PhysicalCoordinateErasureAt.exists_erasure Y L P₀ E
    have hkill (v : (Fin s ⊕ Fin 2) × Fin (L + 1)) (hv : v ∈ E) :
        ActivePhysicalPrimeGroups.label Y L M v = 0 := by
      ext u
      exact hzero u v hv
    let P := fun u : Fin (L + 1) ↦ ActivePhysicalPrimeGroups.label Y L M (Sum.inr 0, u) ≠ 0
    let Q := fun v : Fin (L + 1) ↦ ActivePhysicalPrimeGroups.label Y L M (Sum.inr 1, v) ≠ 0
    have hsafe (w : Fin (L + 1) × Fin (L + 1)) (hw : w ∈ D) : ¬P w.1 ∨ ¬Q w.2 := by
      apply Or.inl
      intro hactive
      exact hactive (hkill (Sum.inr 0, w.1) (mem_union_left _ (mem_image.mpr ⟨w, hw, rfl⟩)))
    have hYZ := hzactive N (by omega) L hband p.1 p.2 (hdyadic p hp).1 (hdyadic p hp).2
      a b ha₀ hb₀ haH hbH hgeomab D (by simp [D]) P Q hsafe
    have hX (i : Fin s ⊕ Fin 2) : Y i ∈ dyadicBlock N := by
      rcases i with i | j
      · exact hx i
      · fin_cases j
        · simpa [Y, starts] using (hdyadic p hp).1
        · simpa [Y, starts] using (hdyadic p hp).2
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hcostR : (Module.finrank F₂ P₀ : ℝ) ≤ E.card + (Module.finrank F₂ M : ℝ) := by
        exact_mod_cast hcost
      have hh := (hdense p hp).2.2
      nlinarith only [hh, hdim₀, hcostR, hEcard, hηL]
    have hmem (j : Fin 2) : Y (Sum.inr j) ∈ U := by
      by_cases hjA : Y (Sum.inr j) ∈ A
      · exact mem_union_right _ hjA
      apply mem_union_left
      have hno : OffsetNonalignmentFrom.NoExactFrom Y L
          (fun v ↦ ActivePhysicalPrimeGroups.label Y L M v ≠ 0) (Sum.inr j) := by
        rintro (i | k) hik u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
        · have hnonSource : ¬ CompressedTargetAlignment.Aligned 1 (x i) (Y (Sum.inr j)) L := by
            intro hh
            exact hjA ((AlignedSourcePool.mem_pool _ x 1 L _).mpr ⟨hX (Sum.inr j), i, hh⟩)
          have hh := ActualOffsetNonalignment.of_nonaligned hL
            (by have hh := (mem_Ico.mp (hx i)).1; omega)
            (by have hh := (mem_Ico.mp (hX (Sum.inr j))).1; omega) hnonSource
          simpa only [Y, starts] using hh.symm u₁ u₂ v₁ v₂ hne
        · fin_cases j <;> fin_cases k
          · exact False.elim (hik rfl)
          · simpa [Y, starts] using hYZ u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
          · have hne' : (NormalizedUnitCount.offset v₁, NormalizedUnitCount.offset u₁) ≠
                (NormalizedUnitCount.offset v₂, NormalizedUnitCount.offset u₂) := by
              intro hh
              exact hne (Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh))
            have hh := hYZ v₁ v₂ u₁ u₂ hv₁ hv₂ hu₁ hu₂ hne'
            simpa [Y, starts, mul_comm] using hh.symm
          · exact False.elim (hik rfl)
      exact hw N (by omega) L hband (Fin s ⊕ Fin 2) (by simp) Y hX M (L + 1)
        le_rfl (Sum.inr j) hno hdim' (hproj (Sum.inr j) (hinj₀ j))
    exact mem_product.mpr ⟨by simpa [Y, starts] using hmem 0, by simpa [Y, starts] using hmem 1⟩
  have hT := hc N (by omega) L (L + 1) (2 * τ * K) hband (by simp)
  have hA := ha N (by omega) L hband x
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA' : (A.card : ℝ) ≤ (N : ℝ) ^ (2 * τ * K + ε / 8) := hA.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [mul_nonneg hτ.le hK]))
  have hU : (U.card : ℝ) ≤ 2 * (N : ℝ) ^ (2 * τ * K + ε / 8) := by
    have hh : (U.card : ℝ) ≤ (T.card : ℝ) + A.card := by exact_mod_cast card_union_le T A
    linarith only [hh, hT, hA']
  have hfinite : (F.card : ℝ) ≤ (U.card : ℝ) ^ 2 := by
    have hh := (card_le_card hsub).trans_eq (card_product U U)
    exact_mod_cast hh.trans_eq (pow_two U.card).symm
  calc
    _ ≤ (U.card : ℝ) ^ 2 := hfinite
    _ ≤ (2 * (N : ℝ) ^ (2 * τ * K + ε / 8)) ^ 2 := pow_le_pow_left₀ (by positivity) hU 2
    _ = 4 * (N : ℝ) ^ (4 * τ * K + ε / 4) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N)]
      norm_num
      congr 1
      ring
    _ ≤ 4 * (N : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hbudget) (by norm_num)
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DenseTwoTargetWeakHosts
