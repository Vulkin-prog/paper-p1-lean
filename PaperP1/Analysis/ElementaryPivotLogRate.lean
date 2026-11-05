module

public import PaperP1.Analysis.ElementaryDyadicPivotLower
public import PaperP1.Analysis.ElementaryReciprocalPivotUpper

/-! # Leading logarithmic rates for the actual reciprocal pivot sums

The leading exponent is one. The fine negative saddle correction is
not obtained from these elementary power and logarithmic bounds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementaryPivotLogRate

open Finset Filter OddPrimePivot ReciprocalOddPivots DyadicOddPivots

theorem full_le (N : ℕ) : pivotSum N ≤ N := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := sum_le_sum (fun n _ ↦ by
      simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by exact_mod_cast largestOddPrime_pos n : (1 : ℝ) ≤ largestOddPrime n))
    _ = _ := by simp

theorem dyadic_le (N : ℕ) : dyadicSum N ≤ N := by
  calc
    _ ≤ ∑ _n ∈ Ico N (2 * N), (1 : ℝ) := sum_le_sum (fun n _ ↦ by
      simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by exact_mod_cast largestOddPrime_pos n : (1 : ℝ) ≤ largestOddPrime n))
    _ = _ := by simp; omega

theorem log_sandwich {N : ℕ} {S ε : ℝ} (hN : 2 ≤ N)
    (hl : (N : ℝ) ^ (1 - ε) ≤ S) (hu : S ≤ N) :
    |Real.log S - Real.log N| ≤ ε * Real.log N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < S := (Real.rpow_pos_of_pos hn (1 - ε)).trans_le hl
  have hloglow := Real.log_le_log (Real.rpow_pos_of_pos hn (1 - ε)) hl
  rw [Real.log_rpow hn] at hloglow
  have hloghigh := Real.log_le_log hs hu
  rw [abs_of_nonpos (sub_nonpos.mpr hloghigh)]
  linarith only [hloglow]

theorem full_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      |Real.log (pivotSum N) - Real.log N| ≤ ε * Real.log N := by
  obtain ⟨N₀, hN₀, h⟩ := ElementaryReciprocalPrimeLower.uniform_lower ε hε
  exact ⟨N₀, hN₀, fun N hN ↦ log_sandwich (by omega) (h N hN) (full_le N)⟩

theorem dyadic_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      |Real.log (dyadicSum N) - Real.log N| ≤ ε * Real.log N := by
  obtain ⟨N₀, hN₀, h⟩ := ElementaryDyadicPivotLower.uniform_lower ε hε
  exact ⟨N₀, hN₀, fun N hN ↦ log_sandwich (by omega) (h N hN) (dyadic_le N)⟩

theorem limit_of_log_bound (S : ℕ → ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      |Real.log (S N) - Real.log N| ≤ ε * Real.log N) :
    Tendsto (fun N : ℕ ↦ Real.log (S N) / Real.log N) atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀, hN₀, h⟩ := hbound (ε / 2) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := h N hN
  have hid : Real.log (S N) / Real.log N - 1 = (Real.log (S N) - Real.log N) / Real.log N := by field_simp
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hlog]
  exact ((div_le_iff₀ hlog).mpr hh).trans_lt (by linarith only [hε])

theorem full_normalized_log_limit :
    Tendsto (fun N : ℕ ↦ Real.log (pivotSum N) / Real.log N) atTop (nhds 1) :=
  limit_of_log_bound pivotSum full_log_bound

theorem dyadic_normalized_log_limit :
    Tendsto (fun N : ℕ ↦ Real.log (dyadicSum N) / Real.log N) atTop (nhds 1) :=
  limit_of_log_bound dyadicSum dyadic_log_bound

end PaperP1.ElementaryPivotLogRate
