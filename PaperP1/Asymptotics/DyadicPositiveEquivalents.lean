module

public import PaperP1.Asymptotics.DyadicPositiveProfiles
public import PaperP1.Asymptotics.DyadicPhaseScale

/-! # Complete actual and global rational dyadic positive equivalents -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPositiveEquivalents

open PaperP1.DyadicPositiveProfiles PaperP1.TwoThreePositivePhase

def reference (N L : ℕ) : ℝ :=
  ((3 : ℝ) + ((L + 1) % 3 : ℕ)) / 18 * N * ((L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((L + 1) / 3)

theorem reference_eq (N L : ℕ) : reference N L = (N : ℝ) / 3 * positiveMain L := by
  unfold reference positiveMain
  ring

theorem reference_pos {N : ℕ} (hN : 0 < N) (L : ℕ) : 0 < reference N L := by
  rw [reference_eq]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (by positivity) (positiveMain_pos L)

theorem reference_eval (N : ℕ) {k r : ℕ} (hk : 1 ≤ k) (hr : r < 3) :
    reference N (3 * k + r - 1) =
      ((3 : ℝ) + r) / 18 * N * ((3 * k + r : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  rw [reference_eq, positiveMain_eval hk hr]
  ring

theorem relative_transfer {a P U F η : ℝ} (ha : 0 ≤ a)
    (hchannel : |U - F| ≤ (η / 2) * F)
    (herror : |P - a * U| ≤ (η / 2) * (a * F)) : |P - a * F| ≤ η * (a * F) := by
  have hh : |a * U - a * F| ≤ (η / 2) * (a * F) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ha]
    have ht := mul_le_mul_of_nonneg_left hchannel ha
    nlinarith only [ht]
  have ht := abs_sub_le P (a * U) (a * F)
  linarith only [ht, hh, herror]

theorem uniform_relative (C η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |positive N L - reference N L| ≤ η * reference N L ∧
      |rational N L - reference N L| ≤ η * reference N L := by
  obtain ⟨NA, hA⟩ := uniform_positive_main C (1 / 24) (by norm_num)
  obtain ⟨NB, hB⟩ := uniform_rational_main C (1 / 24) (by norm_num)
  obtain ⟨NC, hC⟩ := PaperP1.TwoThreePositivePhase.uniform_critical_relative C (η / 2) (by positivity)
  obtain ⟨NE, hE⟩ := PaperP1.DyadicPhaseScale.power_error_negligible C (31 / 24) (η / 2) (by norm_num) (by positivity)
  refine ⟨max NA (max NB (max NC NE)), ?_⟩
  intro N hN L hcrit
  have ha := hA N (by omega) L hcrit
  have hb := hB N (by omega) L hcrit
  norm_num only [show (5 : ℝ) / 4 + 1 / 24 = 31 / 24 by norm_num] at ha hb
  have hc := hC N (by omega) L hcrit
  have he := hE N (by omega) L hcrit
  rw [reference_eq]
  have hn : (0 : ℝ) ≤ (N : ℝ) / 3 := by positivity
  exact ⟨relative_transfer hn hc (ha.trans he), relative_transfer hn hc (hb.trans he)⟩

theorem uniform_ratio (C η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < reference N L ∧
      |rational N L / reference N L - 1| ≤ η ∧
      |positive N L / reference N L - 1| ≤ η := by
  obtain ⟨N₀, hR⟩ := uniform_relative C η hη
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit
  obtain ⟨hp, hr⟩ := hR N hN L hcrit
  have hpos := reference_pos (by omega : 0 < N) L
  have hP : positive N L / reference N L - 1 =
      (positive N L - reference N L) / reference N L := by field_simp
  have hR : rational N L / reference N L - 1 =
      (rational N L - reference N L) / reference N L := by field_simp
  refine ⟨hpos, ?_, ?_⟩
  · rw [hR, abs_div, abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr hr
  · rw [hP, abs_div, abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr hp

end PaperP1.DyadicPositiveEquivalents
