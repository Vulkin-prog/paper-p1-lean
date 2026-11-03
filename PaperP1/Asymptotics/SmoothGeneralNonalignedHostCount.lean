module

public import PaperP1.Asymptotics.GeneralNonalignedRootHostCount
public import PaperP1.Asymptotics.CriticalGeneralRootPatterns
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Summing all actual smooth general split systems over nonaligned hosts

The finite pattern count and coefficient heights are proved internally. Only
the two explicit uniform geometric properties remain unproved arguments.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothGeneralNonalignedHostCount

open Finset PaperP1.GeneralSplitRadicalPatternPool PaperP1.SplitRadicalPointHeight

def Valid {k : ℕ} (K : ℕ) (p : Pattern k) : Prop :=
  (Pairwise fun i t ↦ Disjoint (p.1.1 i) (p.1.1 t)) ∧
    (Pairwise fun i t ↦ Disjoint (p.1.2 i) (p.1.2 t)) ∧
    (∀ i, (p.1.1 i).Nonempty) ∧ (∀ i, (p.1.2 i).Nonempty) ∧
    (∀ i, (p.1.1 i).card + (p.1.2 i).card ≤ K)

theorem uniform_hosts (C ε : ℝ) (D K : ℕ) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k K Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1.natAbs p.2.natAbs L) →
        (∀ p ∈ F, ∃ q ∈ pool k L H K, Valid K q ∧ ∃ w : Fin k → ℤ,
          ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨A₀, Nh, hheight⟩ := CriticalGeneralRootPatterns.uniform_coefficient_height C D
  obtain ⟨Ds, k, hDs, _hdegree, hk⟩ := GeneralNonalignedRootHostCount.source_uniform_hosts_of_many C (A₀ : ℝ) (ε / 2) K
    (Nat.cast_nonneg A₀) (by positivity)
  obtain ⟨Np, hp⟩ := CriticalGeneralRootPatterns.uniform_pool C (ε / 2) D k K (by positivity)
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, max 1 (max Nh (max Np Nc)), ?_⟩
  intro N hN L H hcrit hH F hdyadic hnon hsystems
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let patterns := (pool k L H K).filter (Valid K)
  let hosts := fun q : Pattern k ↦ F.filter fun p ↦ ∃ w : Fin k → ℤ,
    ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2
  have hcover : ∀ p ∈ F, ∃ q ∈ patterns, p ∈ hosts q := by
    intro p hpF
    obtain ⟨q, hq, hvalid, w, hw⟩ := hsystems p hpF
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hpF, w, hw⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε / 2) := by
    intro q hq
    obtain ⟨hqpool, hI, hJ, hneI, hneJ, hK⟩ := mem_filter.mp hq
    exact hcount N (by omega) L hcrit k le_rfl (coefficient q) q.1.1 q.1.2
      (fun i ↦ (coefficient_pos hqpool i).ne') hI hJ hneI hneJ hK (left_bound hqpool) (right_bound hqpool)
      (hheight N (by omega) L H hcrit hH k K q hqpool) (hosts q)
      (fun p hpF ↦ hdyadic p (mem_filter.mp hpF).1)
      (fun p hpF ↦ hnon p (mem_filter.mp hpF).1)
      (fun _ hpF ↦ (mem_filter.mp hpF).2)
  have hfinite := FiniteCoverCount.cardinal_le F patterns hosts (A * (N : ℝ) ^ (1 / 2 + ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool k L H K).card by exact_mod_cast card_filter_le _ _).trans
      (hp N (by omega) L H hcrit hH)
  calc
    _ ≤ (patterns.card : ℝ) * (A * (N : ℝ) ^ (1 / 2 + ε / 2)) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (A * (N : ℝ) ^ (1 / 2 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hpatterns (mul_nonneg hA.le (Real.rpow_nonneg hNpos.le _))
    _ = A * (N : ℝ) ^ (1 / 2 + ε) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos, show ε / 2 + (1 / 2 + ε / 2) = 1 / 2 + ε by ring]

end PaperP1.SmoothGeneralNonalignedHostCount
