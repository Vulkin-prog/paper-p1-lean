module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Coding.LocalDefectWindowScale
public import PaperP1.Model.FiniteRademacher

/-! # Companion T9.2: actual 10B-defective positions in critical windows

This is a specialization of the already proved local defect count. It does
not assume admissibility, positive start probability or regularity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalDefectPositions

open PaperP1.Model LocalDefectBound LargeOddKernel CriticalBandScale Finset

def criticalDefectivePositions (x L : ℕ) : Finset ℕ := by
  classical
  exact (Icc (x - 1) (x + L - 1)).filter fun n ↦ largeOddKernel (10 * (L + 1)) n = 1

theorem mem_criticalDefectivePositions {x L n : ℕ} : n ∈ criticalDefectivePositions x L ↔
    x - 1 ≤ n ∧ n ≤ x + L - 1 ∧ largeOddKernel (10 * (L + 1)) n = 1 := by
  classical
  simp [criticalDefectivePositions, and_assoc]

theorem criticalDefectivePositions_eq_interval {x L : ℕ} (hx : 0 < x) :
    criticalDefectivePositions x L = defectsInInterval (10 * (L + 1)) (x - 1) L := by
  ext n
  rw [mem_criticalDefectivePositions, mem_defectsInInterval,
    ← largeOddKernel_eq_one_iff]
  have hend : x - 1 + L = x + L - 1 := by omega
  rw [hend]

/-- Literal O_C(B/log B), B=L+1, for every dyadic critical window.
One constant and threshold apply before all starts and run lengths. -/
theorem uniform_critical_defect_constant :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
        ((criticalDefectivePositions x L).card : ℝ) ≤
          K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ :=
    LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
      (1 / 2 : ℝ) 2 lowerScale upperScale 10 1
      (by norm_num) (by norm_num) lowerScale_pos upperScale_pos.le (by norm_num) (by norm_num)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  refine ⟨max 2 (max Nscale Nlocal), ?_⟩
  intro N hN L hband x hx
  have hxblock := mem_Ico.mp hx
  have hxpos : 0 < x := by omega
  have hbaseNat : N ≤ 2 * (x - 1) := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    have h : (N : ℝ) ≤ 2 * ((x - 1 : ℕ) : ℝ) := by exact_mod_cast hbaseNat
    linarith
  have hbaseUpper : ((x - 1 : ℕ) : ℝ) ≤ 2 * N := by
    exact_mod_cast (show x - 1 ≤ 2 * N by omega)
  have hsc := hscale N (by omega) L hband
  rw [criticalDefectivePositions_eq_interval hxpos]
  exact hlocal N (by omega) ((L + 1 : ℕ) : ℝ) (10 * (L + 1)) (x - 1) L
    hsc.1 hsc.2 (by norm_num) (by norm_num) hbase hbaseUpper

theorem companion_T9_2 (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
        ((criticalDefectivePositions x L).card : ℝ) ≤
          K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := uniform_critical_defect_constant
  exact ⟨K, hK, hbound C⟩

end PaperP1.CriticalDefectPositions
