module

public import PaperP1.Asymptotics.EnlargedDegreeOneRootHostCount
public import PaperP1.Asymptotics.EnlargedRootPatterns
public import PaperP1.Asymptotics.SmoothDegreeOneHostCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Summing actual smooth systems with the enlarged displacement exclusion

Every offset list and small-prime support is enumerated. The original
critical length is retained independently of the larger offset range.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedSmoothDegreeOneHostCount

open Finset PaperP1.SplitRadicalPatternPool PaperP1.SplitRadicalPointHeight

open PaperP1.SmoothDegreeOneHostCount

theorem uniform_hosts (C ε : ℝ) (D R K : ℕ) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ R * (L + 1) → H ≤ D * (L + 1) →
      ∀ a : ℕ, 0 < a → ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned R p.1.natAbs p.2.natAbs L) →
        (∀ p ∈ F, ∃ q ∈ pool k W H K, Valid a K q ∧ ∃ w : Fin k → ℤ,
          ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * (p.2 + q.1.2 i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨A₀, Nh, hheight⟩ := EnlargedRootPatterns.linear_coefficient_height C D
  obtain ⟨k, hk⟩ := EnlargedDegreeOneRootHostCount.uniform_hosts_of_many C (A₀ : ℝ) (ε / 2) R K
    (Nat.cast_nonneg A₀) (by positivity)
  obtain ⟨Np, hp⟩ := EnlargedRootPatterns.linear_pool C (ε / 2) D 2 k K (by positivity)
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C R
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, max 1 (max Nh (max Np (max Nc Nw))), ?_⟩
  intro N hN L W H hcrit hW hH a ha F hdyadic hnon hsystems
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly := (hw N (by omega) L (W + 1) hcrit hW).1
  let patterns := (pool k W H K).filter (Valid a K)
  let hosts := fun q : Pattern k ↦ F.filter fun p ↦ ∃ w : Fin k → ℤ,
    ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * (p.2 + q.1.2 i)
  have hcover : ∀ p ∈ F, ∃ q ∈ patterns, p ∈ hosts q := by
    intro p hpF
    obtain ⟨q, hq, hvalid, w, hw⟩ := hsystems p hpF
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hpF, w, hw⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ A * (N : ℝ) ^ (ε / 2) := by
    intro q hq
    obtain ⟨hqpool, hI, hj, hcard, hK⟩ := mem_filter.mp hq
    exact hcount N (by omega) L (W + 1) hcrit (by omega) hW k le_rfl (coefficient q) q.1.1 q.1.2 a ha
      (fun i ↦ (coefficient_pos hqpool i).ne') hI hj hcard hK (left_bound hqpool) (right_bound hqpool)
      (hheight N (by omega) L H hcrit hH k W K q hqpool) (hosts q)
      (fun p hpF ↦ hdyadic p (mem_filter.mp hpF).1)
      (fun p hpF ↦ hnon p (mem_filter.mp hpF).1)
      (fun _ hpF ↦ (mem_filter.mp hpF).2)
  have hfinite := FiniteCoverCount.cardinal_le F patterns hosts (A * (N : ℝ) ^ (ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool k W H K).card by exact_mod_cast card_filter_le _ _).trans
      (hp N (by omega) L W H hcrit hpoly hH)
  calc
    _ ≤ (patterns.card : ℝ) * (A * (N : ℝ) ^ (ε / 2)) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (A * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hpatterns (mul_nonneg hA.le (Real.rpow_nonneg hNpos.le _))
    _ = A * (N : ℝ) ^ ε := by
      rw [mul_left_comm, ← Real.rpow_add hNpos, show ε / 2 + ε / 2 = ε by ring]

end PaperP1.EnlargedSmoothDegreeOneHostCount
