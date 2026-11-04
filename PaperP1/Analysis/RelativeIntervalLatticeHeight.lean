module

public import PaperP1.Analysis.RelativeIntervalLattice

/-! # Coefficient heights of the actual source interval lattice and its inverse -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalLatticeHeight

open PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals

theorem entry_heights (Q N : ℕ) (hQ : 1 ≤ Q) (hN : 1 ≤ N) (D E M s : ℝ)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hDN : D ≤ (Q : ℝ) * N) (hEN : E ≤ (Q : ℝ) * N)
    (hs : 0 ≤ s) (hsupper : s ≤ 2 * D / E) :
    (∀ i j, |transform D E M s i j| ≤ (2 : ℝ) * Q * N) ∧
      ∀ i j, |inverse D E M s i j| ≤ (2 : ℝ) * Q * N := by
  have hDp : 0 < D := by linarith
  have hEp : 0 < E := by linarith
  have hMp : 0 < M := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQN : (N : ℝ) ≤ (Q : ℝ) * N := by nlinarith
  have hcommon : 1 ≤ (2 : ℝ) * Q * N := by nlinarith
  have hMD : M / D ≤ M := (div_le_iff₀ hDp).mpr (by nlinarith)
  have hDM : D / M ≤ D := (div_le_iff₀ hMp).mpr (by nlinarith)
  have hEinv : 1 / E ≤ 1 := (div_le_iff₀ hEp).mpr (by linarith)
  have hsE : s * E ≤ 2 * D := (le_div_iff₀ hEp).mp hsupper
  have hsD : s ≤ 2 * D := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hE)]
  have hMs : M * s ≤ (N : ℝ) * (2 * D) := mul_le_mul hMN hsD hs (by positivity)
  have hMsD : M * s / D ≤ (2 : ℝ) * N := (div_le_iff₀ hDp).mpr (by nlinarith)
  have h00 : |M / D| ≤ (2 : ℝ) * Q * N := by
    rw [abs_of_pos (div_pos hMp hDp)]
    nlinarith
  have h01 : |-M * s / D| ≤ (2 : ℝ) * Q * N := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hMp, abs_of_nonneg hs, abs_of_pos hDp]
    nlinarith
  have h11 : |1 / E| ≤ (2 : ℝ) * Q * N := by
    rw [abs_of_pos (one_div_pos.mpr hEp)]
    linarith
  have hg00 : |D / M| ≤ (2 : ℝ) * Q * N := by
    rw [abs_of_pos (div_pos hDp hMp)]
    linarith
  have hg01 : |s * E| ≤ (2 : ℝ) * Q * N := by
    rw [abs_of_nonneg (mul_nonneg hs hEp.le)]
    linarith
  have hg11 : |E| ≤ (2 : ℝ) * Q * N := by rw [abs_of_pos hEp]; linarith
  have hz : (0 : ℝ) ≤ 2 * Q * N := by positivity
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [transform] using h00
    · simpa [transform] using h01
    · simpa [transform] using hz
    · simpa [transform] using h11
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [inverse] using hg00
    · simpa [inverse] using hg01
    · simpa [inverse] using hz
    · simpa [inverse] using hg11

theorem uniform_power_heights (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D E M s : ℝ,
      1 ≤ D → 1 ≤ E → 1 ≤ M → M ≤ N → D ≤ (Q : ℝ) * N → E ≤ (Q : ℝ) * N →
      0 ≤ s → s ≤ 2 * D / E →
      (∀ i j, |transform D E M s i j| ≤ ((N ^ 2 : ℕ) : ℝ)) ∧
      ∀ i j, |inverse D E M s i j| ≤ ((N ^ 2 : ℕ) : ℝ) := by
  refine ⟨max 2 (2 * Q), ?_⟩
  intro N hN D E M s hD hE hM hMN hDN hEN hs hsupper
  have hN1 : 1 ≤ N := by omega
  have hQN : (2 : ℝ) * Q ≤ N := by exact_mod_cast (show 2 * Q ≤ N by omega)
  have hlarge : (2 : ℝ) * Q * N ≤ ((N ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hQN (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h := entry_heights Q N hQ hN1 D E M s hD hE hM hMN hDN hEN hs hsupper
  exact ⟨fun i j ↦ (h.1 i j).trans hlarge, fun i j ↦ (h.2 i j).trans hlarge⟩

theorem interval_center_range (M k : ℕ) (hM : 0 < M) (hk : k ≤ 2 * M)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) :
    0 ≤ intervalCenter M D E k ∧ intervalCenter M D E k ≤ 2 * D / E := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hkR : (k : ℝ) ≤ 2 * M := by exact_mod_cast hk
  constructor
  · unfold intervalCenter
    positivity
  · unfold intervalCenter
    apply (div_le_iff₀ hMR).mpr
    have h := mul_le_mul_of_nonneg_left hkR (div_pos hD hE).le
    convert h using 1
    ring

end PaperP1.RelativeIntervalLatticeHeight
