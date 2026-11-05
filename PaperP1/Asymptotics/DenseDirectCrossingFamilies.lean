module

public import PaperP1.Asymptotics.DirectCrossingExtensions
public import PaperP1.Asymptotics.CriticalActualMean

/-! # Summing all remaining sources proves the actual dense direct-crossing family cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseDirectCrossingFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem uniform_families (r s : ℕ) (hr : 2 ≤ r) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ A ∈ F, A ⊆ G \ e ∧ A.card = r ∧ runRelativeNullity L A = 0 ∧
        (∀ B : Finset ℕ, B ⊂ A →
          Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B)) ∧
        η * L ≤ (MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
          (fun x ↦ squareClassSpace x L) A : ℝ)) →
      (∑ A ∈ F, infiniteJointMoment L (e ∪ A)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨ND, _hND, hd⟩ := DirectCrossingExtensions.uniform_extensions (s + r - 2)
    C η (ε / 2) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (Real.exp (2 * (2 : ℝ) ^ C))
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NM + NF + ND, by omega, ?_⟩
  intro N hN L hband e hecard heG G hG F hF
  let T := (G \ e).powersetCard (r - 2)
  let w := fun A : Finset ℕ ↦ infiniteJointMoment L (e ∪ A)
  have hcover := TwoTargetFamilyCover.weighted_cover (G \ e) T F w
    (fun A ↦ infiniteJointMoment_nonneg L _) (fun A hA ↦ (hF A hA).1) (by
      intro B hB A hA
      have hBc := (mem_powersetCard.mp hB).2
      have hAc := (hF A hA).2.1
      omega) (by
      intro A hA
      have hAc := (hF A hA).2.1
      obtain ⟨B, hBA, hBc⟩ := exists_subset_card_eq (show r - 2 ≤ A.card by omega)
      exact ⟨B, mem_powersetCard.mpr ⟨hBA.trans (hF A hA).1, hBc⟩, hBA⟩)
  change (∑ A ∈ F, infiniteJointMoment L (e ∪ A)) ≤
    ∑ B ∈ T, ∑ p ∈ TwoTargetFamilyCover.pairs (G \ e) B F,
      infiniteJointMoment L (e ∪ TwoTargetFamilyCover.family B p) at hcover
  simp_rw [DirectCrossingTargets.union_family] at hcover
  have hbound (B : Finset ℕ) (hB : B ∈ T) :
      (∑ p ∈ TwoTargetFamilyCover.pairs (G \ e) B F,
        infiniteJointMoment L (TwoTargetFamilyCover.family (e ∪ B) p)) ≤
        (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) * (N : ℝ) ^ (-1 + ε / 2) := by
    obtain ⟨hBG, hBc⟩ := mem_powersetCard.mp hB
    have heB : Disjoint e B := disjoint_left.mpr fun x hxE hxB ↦ (mem_sdiff.mp (hBG hxB)).2 hxE
    have hcard : (e ∪ B).card = s + r - 2 := by rw [card_union_of_disjoint heB, hecard, hBc]; omega
    apply hd N (by omega) L hband e B hcard (union_subset heG (hBG.trans (sdiff_subset.trans hG))) heB
    · intro p hp
      obtain ⟨hy, hz, hyz, hyB, hzB, _hfamily⟩ := (TwoTargetFamilyCover.mem_pairs _ B F p).mp hp
      exact ⟨hG (mem_sdiff.mp hy).1, hG (mem_sdiff.mp hz).1, hyz,
        fun h ↦ (not_or.mpr ⟨(mem_sdiff.mp hy).2, hyB⟩) (mem_union.mp h),
        fun h ↦ (not_or.mpr ⟨(mem_sdiff.mp hz).2, hzB⟩) (mem_union.mp h)⟩
    · intro p hp
      have hfamily := (TwoTargetFamilyCover.mem_pairs _ B F p).mp hp
      have hA := hF _ hfamily.2.2.2.2.2
      exact ⟨hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩
  have hmean : (∑ x ∈ G \ e, infiniteMarginal x L) ≤ 2 * (2 : ℝ) ^ C := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans hG)
      (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
    have h := (hm N (by omega) L hband).2
    rwa [CountObservables.countMoment_one Subset.rfl] at h
  have hsum : (∑ B ∈ T, ∏ x ∈ B, infiniteMarginal x L) ≤ Real.exp (2 * (2 : ℝ) ^ C) := by
    calc
      _ ≤ ∑ B ∈ (G \ e).powerset, ∏ x ∈ B, infiniteMarginal x L :=
        sum_le_sum_of_subset_of_nonneg (fun B hB ↦ mem_powerset.mpr (mem_powersetCard.mp hB).1)
          (fun B _ _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = ∏ x ∈ G \ e, (1 + infiniteMarginal x L) := by rw [prod_one_add]
      _ ≤ Real.exp (∑ x ∈ G \ e, infiniteMarginal x L) :=
        Real.prod_one_add_le_exp_sum _ (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ ≤ _ := Real.exp_le_exp.mpr hmean
  have hfactor : Real.exp (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2) ≤
      (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  calc
    _ ≤ ∑ B ∈ T, (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) *
        (N : ℝ) ^ (-1 + ε / 2) := hcover.trans (sum_le_sum hbound)
    _ = (infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2)) *
        ∑ B ∈ T, ∏ x ∈ B, infiniteMarginal x L := by
      rw [mul_sum]
      apply sum_congr rfl
      intro B _
      ring
    _ ≤ (infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2)) * Real.exp (2 * (2 : ℝ) ^ C) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (infiniteJointMoment_nonneg L e)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = infiniteJointMoment L e * (Real.exp (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (infiniteJointMoment_nonneg L e)

end PaperP1.DenseDirectCrossingFamilies
