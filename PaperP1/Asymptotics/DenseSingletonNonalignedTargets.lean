module

public import PaperP1.Asymptotics.DensePhysicalKernelWitnessAt
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization
public import PaperP1.Asymptotics.CriticalTwoPointClasses
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.TwoTargetJointWeight

/-! # Unconditional dense nonaligned target pairs above one actual source window

Only the target projections must be injective. The source window itself is
kept in full, and is direct from each target separately.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseSingletonNonalignedTargets

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
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
        Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L (squareClassSpace x L)) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, ht, hreg⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace 1 η hη
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
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NW + NC + NR + NG, by omega, ?_⟩
  intro N hN L hband x hx F hdyadic hnon hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  let T := SmallKernelWindowSets.twoWindows N L (L + 1) (2 * τ * K)
  have hsub : F ⊆ T ×ˢ T := by
    intro p hp
    let X : Fin 1 → ℕ := fun _ ↦ x
    have hW : squareClassSpace x L ≤ ⨆ i, squareClassSpace (X i) L :=
      le_iSup (fun _ : Fin 1 ↦ squareClassSpace x L) 0
    obtain ⟨M, hrec, hdim, hinj⟩ := hreg X p.1 p.2 L hL (squareClassSpace x L) hW
      (hdense p hp).1 (hdense p hp).2.1
    have hX : ∀ i, starts X p.1 p.2 i ∈ dyadicBlock N := by
      rintro (i | j)
      · exact hx
      · fin_cases j
        · simpa [starts] using (hdyadic p hp).1
        · simpa [starts] using (hdyadic p hp).2
    have hxy := hr N (by omega) L hband x p.1 (mem_Ico.mp hx).1
      (mem_Ico.mp (hdyadic p hp).1).1 (hdense p hp).1
    have hxz := hr N (by omega) L hband x p.2 (mem_Ico.mp hx).1
      (mem_Ico.mp (hdyadic p hp).2).1 (hdense p hp).2.1
    have hyz := ActualOffsetNonalignment.of_nonaligned (by omega : 1 ≤ L)
      (by have hh := (mem_Ico.mp (hdyadic p hp).1).1; omega)
      (by have hh := (mem_Ico.mp (hdyadic p hp).2).1; omega) (hnon p hp)
    have hno : ∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact
        (starts X p.1 p.2 i) (starts X p.1 p.2 j) L := by
      rintro (i | i) (j | j) hij
      · have he : i = j := Subsingleton.elim _ _
        subst j
        exact False.elim (hij rfl)
      · fin_cases j
        · simpa [starts, X] using hxy
        · simpa [starts, X] using hxz
      · fin_cases i
        · simpa [starts, X] using hxy.symm
        · simpa [starts, X] using hxz.symm
      · fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · simpa [starts] using hyz
        · simpa [starts] using hyz.symm
        · exact False.elim (hij rfl)
    have hdim' : (η / 2) * L ≤ (Module.finrank F₂ M : ℝ) := by
      have hh := (hdense p hp).2.2
      have hn : 0 ≤ η * L := by positivity
      linarith only [hh, hdim, hn]
    have hsmall (j : Fin 2) := hw N (by omega) L hband (Fin 1 ⊕ Fin 2) (by simp)
      (starts X p.1 p.2) hX M (L + 1) le_rfl
      (OffsetNonalignmentOn.of_global _ L _ hno) hrec hdim' (Sum.inr j) (hinj j)
    exact mem_product.mpr ⟨by simpa only [starts, Fin.isValue, ite_true] using hsmall 0,
      by simpa only [starts, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hsmall 1⟩
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
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
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
  intro N hN L hband x hx F hdyadic hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hh N (by omega) L hband x hx F hdyadic hnon hdense
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
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
        Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
          SubspaceFamilyRank.span (fun y ↦ squareClassSpace y L) {p.1, p.2}) : ℝ)) →
      (∑ p ∈ F, infiniteJointMoment L (TwoTargetFamilyCover.family {x} p)) ≤
        infiniteMarginal x L * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass C η ε hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NM + NG, by omega, ?_⟩
  intro N hN L hband x hx F hdata hnon hdense
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hsource : TwoTargetPrimitiveData.sourceSpace {x} L = squareClassSpace x L := by
    simp [TwoTargetPrimitiveData.sourceSpace, SubspaceFamilyRank.span]
  have hmass := hm N (by omega) L hband x hx F
    (fun p hp ↦ ⟨(hdata p hp).1, (hdata p hp).2.1⟩) hnon (by
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

end PaperP1.DenseSingletonNonalignedTargets
