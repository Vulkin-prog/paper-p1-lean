module

public import PaperP1.Asymptotics.DenseSingletonJointMass
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Combinatorics.RestrictedSingletonPairCover
public import PaperP1.Affine.ProperPairCrossing

/-! # Dense triples with a vertex direct from each other vertex have actual joint mass N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IsolatedVertexDenseTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem uniform_mass (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ G ∧ T.card = 3) →
      (∀ T ∈ F, ∃ x ∈ T,
        (∀ y ∈ T.erase x, Disjoint (squareClassSpace x L) (squareClassSpace y L)) ∧
        η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
          span (fun y ↦ squareClassSpace y L) (T.erase x)) : ℝ)) →
      (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨ND, _hND, hd⟩ := DenseSingletonJointMass.uniform_joint C η (ε / 2) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * (2 : ℝ) ^ C)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NM + NF + ND, by omega, ?_⟩
  intro N hN L hband G hG F hF hisolated
  let R := fun x : ℕ ↦ fun T : Finset ℕ ↦
    (∀ y ∈ T.erase x, Disjoint (squareClassSpace x L) (squareClassSpace y L)) ∧
      η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
        span (fun y ↦ squareClassSpace y L) (T.erase x)) : ℝ)
  let P := fun x ↦ TwoTargetFamilyCover.pairs G {x} (RestrictedSingletonPairCover.fibers F R x)
  have hcover := RestrictedSingletonPairCover.weighted_cover G F R (infiniteJointMoment L)
    (infiniteJointMoment_nonneg L) hF hisolated
  have hdata (x : ℕ) (q : ℕ × ℕ) (hq : q ∈ P x) :
      Disjoint (squareClassSpace x L) (squareClassSpace q.1 L) ∧
      Disjoint (squareClassSpace x L) (squareClassSpace q.2 L) ∧
      η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
        span (fun y ↦ squareClassSpace y L) {q.1, q.2}) : ℝ) := by
    obtain ⟨_hy, _hz, _hyz, hyx, hzx, hqF⟩ := (TwoTargetFamilyCover.mem_pairs _ _ _ q).mp hq
    have hr : R x (TwoTargetFamilyCover.family {x} q) :=
      ((RestrictedSingletonPairCover.mem_fibers F R x _).mp hqF).2.2
    have heq := RestrictedSingletonPairCover.erase_source x q (by simpa using hyx) (by simpa using hzx)
    change (∀ y ∈ (TwoTargetFamilyCover.family {x} q).erase x, _) ∧ _ at hr
    rw [heq] at hr
    exact ⟨hr.1 q.1 (mem_insert_self _ _), hr.1 q.2 (mem_insert_of_mem (mem_singleton_self _)), hr.2⟩
  have hcell (x : ℕ) (hx : x ∈ G) :
      (∑ q ∈ P x, infiniteJointMoment L (TwoTargetFamilyCover.family {x} q)) ≤
        infiniteMarginal x L * (N : ℝ) ^ (-1 + ε / 2) := by
    have hs : TwoTargetPrimitiveData.sourceSpace {x} L = squareClassSpace x L := by
      simp [TwoTargetPrimitiveData.sourceSpace, span]
    rw [← InfiniteTripleCancellation.singleton_joint L x]
    apply hd N (by omega) L hband {x} (by simp) (singleton_subset_iff.mpr (hG hx)) (P x)
    · intro q hq
      obtain ⟨hy, hz, hneq, hyE, hzE, _hF⟩ := (TwoTargetFamilyCover.mem_pairs _ _ _ q).mp hq
      exact ⟨hG hy, hG hz, hneq, hyE, hzE⟩
    · intro q hq B hB
      rw [hs]
      exact ProperPairCrossing.proper_direct (fun y ↦ squareClassSpace y L) _ q.1 q.2
        (hdata x q hq).1 (hdata x q hq).2.1 B hB
    · intro q hq
      rw [hs]
      exact (hdata x q hq).2.2
  have hmean : (∑ x ∈ G, infiniteMarginal x L) ≤ 2 * (2 : ℝ) ^ C := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hG
      (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
    have h := (hm N (by omega) L hband).2
    rwa [CountObservables.countMoment_one Subset.rfl] at h
  calc
    _ ≤ ∑ x ∈ G, infiniteMarginal x L * (N : ℝ) ^ (-1 + ε / 2) := hcover.trans (sum_le_sum hcell)
    _ = (∑ x ∈ G, infiniteMarginal x L) * (N : ℝ) ^ (-1 + ε / 2) := (sum_mul ..).symm
    _ ≤ (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_right hmean (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

end PaperP1.IsolatedVertexDenseTripleMass
