module

public import PaperP1.Asymptotics.DenseSingletonNonalignedTargets
public import PaperP1.Arithmetic.PhysicalCoordinateErasureAt
public import PaperP1.Arithmetic.PhysicalSubspaceRegularizationAt
public import PaperP1.Asymptotics.WeakAlignedActiveNonalignment
public import PaperP1.Asymptotics.WeakAlignmentUnitCount
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization
public import PaperP1.Asymptotics.CriticalTwoPointClasses
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.TwoTargetJointWeight

/-! # Unconditional dense weakly aligned target pairs above one actual source window

A fresh regularization follows exact unit erasure. The source window itself is
kept in full, and is direct from each target separately.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseSingletonWeakTargets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PhysicalWindowRelations PaperP1.TwoTargetWindowSections

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)
local instance codeAddCommGroup {L : ℕ} (X : Fin 1 ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin 1 ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {L : ℕ} (X : Fin 1 ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P

theorem uniform_hosts (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
        Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨_t₀, _ht₀, hreg₀⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace 1 (η / 4) (by positivity)
  obtain ⟨t, ht, hreg⟩ := PhysicalSubspaceRegularizationAt.uniform_subspace (η / 4) (by positivity)
  let K : ℝ := PhysicalLabelSupportCount.supportBound 2 t (t - 1)
  let τ := ε / (16 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτeq : τ * (16 * (K + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hbudget : 4 * τ * K + ε / 2 ≤ ε := by nlinarith only [hτeq, hτ.le, hε]
  obtain ⟨NW, _hNW, hw⟩ := DensePhysicalKernelWitnessAt.uniform_witness
    C τ (η / 2) hτ (by positivity) 2 t (by omega) (by omega) ht
  obtain ⟨NC, hcount⟩ := SmallKernelWindows.critical_two_count 1 C (ε / 4) (by norm_num) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := CriticalTwoPointClasses.uniform_disjoint_no_exact C
  obtain ⟨NU, _hNU, hu⟩ := WeakAlignmentUnitCount.uniform_weak_bound C
  obtain ⟨NA, _hNA, ha⟩ := WeakAlignedActiveNonalignment.uniform_no_exact C
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (32 / η)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨3 + NW + NC + NR + NU + NA + NG, by omega, ?_⟩
  intro N hN L hband x hx F hdyadic hweak hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hηL : (32 : ℝ) ≤ η * L := by
    have hprod := (div_lt_iff₀ hη).mp hL₀
    have hlength : (L₀ : ℝ) ≤ L := by exact_mod_cast (show L₀ ≤ L by omega)
    have hm := mul_le_mul_of_nonneg_left hlength hη.le
    nlinarith only [hprod, hm]
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T ×ˢ T := by
    intro p hp
    let X : Fin 1 → ℕ := fun _ ↦ x
    let Y := starts X p.1 p.2
    have hW : squareClassSpace x L ≤ ⨆ i, squareClassSpace (X i) L :=
      le_iSup (fun _ : Fin 1 ↦ squareClassSpace x L) 0
    obtain ⟨P₀, _hrec₀, hdim₀, hinj₀⟩ := hreg₀ X p.1 p.2 L hL (squareClassSpace x L) hW
      (hdense p hp).1 (hdense p hp).2.1
    obtain ⟨a, b, ha₀, hb₀, _hcop, haH, hbH, hab⟩ := (hweak p hp).1
    have hgeomab : EnlargedPairGeometry.Geometric a b p.1 p.2 L := by
      simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hab
    let D := NormalizedUnitCount.units a b p.1 p.2 L
    let E := TwoTargetUnitExclusion.unitEndpoints (s := 1) D
    have hDcard := hu N (by omega) L hband p.1 p.2 (hdyadic p hp).1 (hdyadic p hp).2
      (η / 64) (hweak p hp).2 a b ha₀ hb₀
    have hEcard : (E.card : ℝ) ≤ 2 * (η / 64) * L + 4 := by
      have hh : (E.card : ℝ) ≤ 2 * (D.card : ℝ) := by
        exact_mod_cast TwoTargetUnitExclusion.endpoints_card (s := 1) D
      nlinarith only [hh, hDcard]
    obtain ⟨R, _hRP, hcost, hzero, hprojR⟩ := PhysicalCoordinateErasureAt.exists_erasure Y L P₀ E
    obtain ⟨M, hMR, hrec, hdim, hprojM⟩ := hreg (Fin 1 ⊕ Fin 2) (by simp) Y L hL R
    have hkill (v : (Fin 1 ⊕ Fin 2) × Fin (L + 1)) (hv : v ∈ E) :
        ActivePhysicalPrimeGroups.label Y L M v = 0 := by
      ext u
      exact hzero ⟨u.val, hMR u.property⟩ v hv
    let P := fun u : Fin (L + 1) ↦ ActivePhysicalPrimeGroups.label Y L M (Sum.inr 0, u) ≠ 0
    let Q := fun v : Fin (L + 1) ↦ ActivePhysicalPrimeGroups.label Y L M (Sum.inr 1, v) ≠ 0
    have hsafe (w : Fin (L + 1) × Fin (L + 1)) (hw : w ∈ D) : ¬P w.1 ∨ ¬Q w.2 := by
      apply Or.inl
      intro hactive
      exact hactive (hkill (Sum.inr 0, w.1) (mem_union_left _ (mem_image.mpr ⟨w, hw, rfl⟩)))
    have hYZ := ha N (by omega) L hband p.1 p.2 (hdyadic p hp).1 (hdyadic p hp).2
      a b ha₀ hb₀ haH hbH hgeomab D (by simp [D]) P Q hsafe
    have hxy := hr N (by omega) L hband x p.1 (mem_Ico.mp hx).1
      (mem_Ico.mp (hdyadic p hp).1).1 (hdense p hp).1
    have hxz := hr N (by omega) L hband x p.2 (mem_Ico.mp hx).1
      (mem_Ico.mp (hdyadic p hp).2).1 (hdense p hp).2.1
    have hno : OffsetNonalignmentOn.NoExactOn Y L
        (fun v ↦ ActivePhysicalPrimeGroups.label Y L M v ≠ 0) := by
      rintro (i | i) (j | j) hij u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
      · have he : i = j := Subsingleton.elim _ _
        subst j
        exact False.elim (hij rfl)
      · fin_cases j
        · simpa [Y, starts, X] using hxy u₁ u₂ v₁ v₂ hne
        · simpa [Y, starts, X] using hxz u₁ u₂ v₁ v₂ hne
      · fin_cases i
        · simpa [Y, starts, X] using hxy.symm u₁ u₂ v₁ v₂ hne
        · simpa [Y, starts, X] using hxz.symm u₁ u₂ v₁ v₂ hne
      · fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · simpa [Y, starts] using hYZ u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
        · have hne' : (NormalizedUnitCount.offset v₁, NormalizedUnitCount.offset u₁) ≠
              (NormalizedUnitCount.offset v₂, NormalizedUnitCount.offset u₂) := by
            intro hh
            exact hne (Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh))
          have hh := hYZ v₁ v₂ u₁ u₂ hv₁ hv₂ hu₁ hu₂ hne'
          simpa [Y, starts, mul_comm] using hh.symm
        · exact False.elim (hij rfl)
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hcostR : (Module.finrank F₂ P₀ : ℝ) ≤ E.card + (Module.finrank F₂ R : ℝ) := by exact_mod_cast hcost
      have hh := (hdense p hp).2.2
      nlinarith only [hh, hdim₀, hcostR, hdim, hEcard, hηL]
    have hX : ∀ i, Y i ∈ dyadicBlock N := by
      rintro (i | j)
      · exact hx
      · fin_cases j
        · simpa [Y, starts] using (hdyadic p hp).1
        · simpa [Y, starts] using (hdyadic p hp).2
    have hsmall (j : Fin 2) := hw N (by omega) L hband (Fin 1 ⊕ Fin 2) (by simp)
      Y hX M (L + 1) le_rfl hno hrec hdim' (Sum.inr j)
      (hprojM (Sum.inr j) (hprojR (Sum.inr j) (hinj₀ j)))
    exact mem_product.mpr ⟨by simpa only [Y, starts, Fin.isValue, ite_true] using hsmall 0,
      by simpa only [Y, starts, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hsmall 1⟩
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

theorem uniform_mass (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
        Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ)) →
      (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := uniform_hosts C η (ε / 2) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  let M := 2 * (2 : ℝ) ^ C
  let K := M ^ 2 * (2 : ℝ) ^ C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NM + NA, by omega, ?_⟩
  intro N hN L hband x hx F hdyadic hweak hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hh N (by omega) L hband x hx F hdyadic hweak hdense
  have hpoint (p : ℕ × ℕ) (hp : p ∈ F) :
      infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ) ≤ K / N := by
    have hy := hm N (by omega) L hband p.1 (hdyadic p hp).1
    have hz := hm N (by omega) L hband p.2 (hdyadic p hp).2
    have hprod : infiniteMarginal p.1 L * infiniteMarginal p.2 L ≤ (M / N) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hy hz
        (MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L) (by positivity : 0 ≤ M / N)
    have hdim := dimension_le_length p.1 p.2 L (squareClassSpace x L) (hdense p hp).2.1
    have hpow := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdim).trans
      (CriticalChannelPowers.word_upper (by omega : 2 ≤ N) hband)
    calc
      _ ≤ (M / N) ^ 2 * ((2 : ℝ) ^ C * N) := mul_le_mul hprod hpow (by positivity) (by positivity)
      _ = _ := by dsimp [K]; field_simp
  calc
    _ ≤ ∑ _p ∈ F, K / N := sum_le_sum hpoint
    _ = (F.card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (K / N) := mul_le_mul_of_nonneg_right hcard (by dsimp [K]; positivity)
    _ = K * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [show -1 + ε / 2 = ε / 2 - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring


theorem uniform_joint (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
        p.1 ≠ p.2 ∧ p.1 ≠ x ∧ p.2 ≠ x) →
      (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
        Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
          SubspaceFamilyRank.span (fun y ↦ squareClassSpace y L) {p.1, p.2}) : ℝ)) →
      (∑ p ∈ F, infiniteJointMoment L (TwoTargetFamilyCover.family {x} p)) ≤
        infiniteMarginal x L * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass C η ε hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NM + NG, by omega, ?_⟩
  intro N hN L hband x hx F hdata hweak hdense
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hsource : TwoTargetPrimitiveData.sourceSpace {x} L = squareClassSpace x L := by
    simp [TwoTargetPrimitiveData.sourceSpace, SubspaceFamilyRank.span]
  have hmass := hm N (by omega) L hband x hx F
    (fun p hp ↦ ⟨(hdata p hp).1, (hdata p hp).2.1⟩) hweak (by
      intro p hp
      have hd := hdense p hp
      have hlo := TwoTargetJointWeight.intersection_le_kernel L {x} p.1 p.2 (hdata p hp).2.2.1
      rw [hsource] at hlo
      have hloR : (Module.finrank F₂ ↥(squareClassSpace x L ⊓
          SubspaceFamilyRank.span (fun y ↦ squareClassSpace y L) {p.1, p.2}) : ℝ) ≤
          Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) := by exact_mod_cast hlo
      exact ⟨hd.1, hd.2.1, hd.2.2.trans hloR⟩)
  calc
    _ ≤ ∑ p ∈ F, infiniteMarginal x L * (infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hbound := TwoTargetJointWeight.joint_bound L hL {x} p.1 p.2
        (by simpa only [mem_singleton] using (hdata p hp).2.2.2.1)
        (by simpa only [mem_singleton] using (hdata p hp).2.2.2.2) (hdata p hp).2.2.1
      rw [hsource, InfiniteTripleCancellation.singleton_joint] at hbound
      exact hbound
    _ = infiniteMarginal x L * ∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (MissingBlockProbabilities.infiniteMarginal_nonneg x L)

end PaperP1.DenseSingletonWeakTargets
