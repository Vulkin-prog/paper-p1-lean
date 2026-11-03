module

public import PaperP1.Asymptotics.CoefficientNonalignedHostCount
public import PaperP1.Asymptotics.GeneralRootHostCount
public import PaperP1.Arithmetic.CoefficientPatternGrids

/-! # The pooled half-power host count on actual selected admissible grids requires no global nonalignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoefficientSelectedHostCount

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.CriticalCoefficientPatterns
  PaperP1.CoefficientPatternGrids PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k K Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 2) k →
        (∀ d ∈ Q, 0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, ∃ q ∈ pool k L K Q, CoefficientNonalignedHostCount.Valid K q ∧
          SourceCurvePointCover.Admissible (left q) (right q) p ∧ ∃ w : Fin k → ℤ,
            ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, _hdegree, hk⟩ := GeneralRootHostCount.uniform_hosts_of_many
    C A₀ (ε / 2) K 1 hA₀ (by positivity)
  obtain ⟨Np, _hNp, hp⟩ := CriticalCoefficientPatterns.uniform_pool C (ε / 2) k K (by positivity)
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, max 1 (max Np Nc), ?_⟩
  intro N hN L hcrit Q hQcard hQ F hdyadic hsystems
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let patterns := (pool k L K Q).filter (CoefficientNonalignedHostCount.Valid K)
  let hosts := fun q : Pattern k ↦ F.filter fun p ↦ SourceCurvePointCover.Admissible (left q) (right q) p ∧
    ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2
  have hcover : ∀ p ∈ F, ∃ q ∈ patterns, p ∈ hosts q := by
    intro p hpF
    obtain ⟨q, hq, hvalid, hadmiss, w, hw⟩ := hsystems p hpF
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hpF, hadmiss, w, hw⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε / 2) := by
    intro q hq
    obtain ⟨hqpool, hI, hJ, hneI, hneJ, hK⟩ := mem_filter.mp hq
    have hheight (i : Fin k) : ((coefficient q i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀ := by
      simpa only [coefficient, Int.natAbs_natCast] using (hQ _ (coefficient_mem hqpool i)).2
    exact hcount N (by omega) L (L + 1) hcrit (by omega) (by simp) k le_rfl (coefficient q) q.1.1 q.1.2
      (fun i ↦ (coefficient_pos (fun d hd ↦ (hQ d hd).1) hqpool i).ne') hI hJ hneI hneJ hK
      (left_bound hqpool) (right_bound hqpool) hheight (left q) (right q) (left_subset q) (right_subset q) (hosts q)
      (fun _ hpF ↦ (mem_filter.mp hpF).2.1)
      (fun p hpF ↦ ⟨(hdyadic p (mem_filter.mp hpF).1).2.2.1, (hdyadic p (mem_filter.mp hpF).1).2.2.2⟩)
      (fun _ hpF ↦ (mem_filter.mp hpF).2.2)
  have hfinite := FiniteCoverCount.cardinal_le F patterns hosts (A * (N : ℝ) ^ (1 / 2 + ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool k L K Q).card by exact_mod_cast card_filter_le _ _).trans
      (hp N (by omega) L hcrit Q hQcard)
  calc
    _ ≤ (patterns.card : ℝ) * (A * (N : ℝ) ^ (1 / 2 + ε / 2)) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (A * (N : ℝ) ^ (1 / 2 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hpatterns (mul_nonneg hA.le (Real.rpow_nonneg hNpos.le _))
    _ = A * (N : ℝ) ^ (1 / 2 + ε) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos, show ε / 2 + (1 / 2 + ε / 2) = 1 / 2 + ε by ring]

end PaperP1.CoefficientSelectedHostCount
