module

public import PaperP1.Arithmetic.QuadraticIntervalGrid

/-! # Uniform error after replacing the quadratic center by its actual integer grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticRelativeError

theorem alpha_perturbation_bound (M : ℕ) (hM : 4 ≤ M) {α : ℝ}
    (hα : |α| ≤ 4 / M) : |2 * α + α ^ 2| ≤ 12 / (M : ℝ) := by
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hmp : (0 : ℝ) < M := by linarith
  have ha1 : |α| ≤ 1 := hα.trans ((div_le_one hmp).mpr hm)
  have hs : α ^ 2 ≤ |α| := by nlinarith [sq_abs α, abs_nonneg α]
  calc
    |2 * α + α ^ 2| ≤ |2 * α| + |α ^ 2| := abs_add_le _ _
    _ = 2 * |α| + α ^ 2 := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg α)]
    _ ≤ 12 / (M : ℝ) := by
      calc
        _ ≤ 3 * |α| := by linarith
        _ ≤ 3 * (4 / (M : ℝ)) := mul_le_mul_of_nonneg_left hα (by norm_num)
        _ = _ := by ring

theorem beta_at_interval_scale (M : ℕ) (hM : 0 < M) {h N ρ β : ℝ}
    (hN : 0 < N) (hρ : 0 < ρ) (hMh : (M : ℝ) * |h| ≤ N)
    (hβ : |β| ≤ 4 * |h| / (ρ * N)) : |β| ≤ 4 / (ρ * M) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  apply hβ.trans
  apply (div_le_div_iff₀ (mul_pos hρ hN) (mul_pos hρ hm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hMh (show 0 ≤ 4 * ρ by positivity)]

theorem quadratic_center_bound (M k : ℕ) (hM : 0 < M) (hk : k ≤ 2 * M)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r * ((k : ℝ) / M) ^ 2 ∧ r * ((k : ℝ) / M) ^ 2 ≤ 4 * r := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hkr : (k : ℝ) ≤ 2 * M := by exact_mod_cast hk
  have hdiv : (k : ℝ) / M ≤ 2 := (div_le_iff₀ hm).mpr hkr
  have hdiv0 : 0 ≤ (k : ℝ) / M := div_nonneg (Nat.cast_nonneg _) hm.le
  have hs : ((k : ℝ) / M) ^ 2 ≤ 4 := by nlinarith
  exact ⟨by positivity, by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs hr⟩

theorem relative_grid_error (M k : ℕ) (hM : 4 ≤ M) (hk : k ≤ 2 * M)
    {r ρ α β t : ℝ} (hr : 0 ≤ r) (_hρ : 0 < ρ) (hα : |α| ≤ 4 / M)
    (hβ : |β| ≤ 4 / (ρ * M))
    (ht : t = r * ((k : ℝ) / M) ^ 2 * (1 + 2 * α + α ^ 2 + β)) :
    |t - r * ((PaperP1.QuadraticIntervalGrid.grid M k : ℝ) / M)| ≤
      r * (49 + 16 / ρ) / M := by
  have hMp : 0 < M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast hMp
  have ha := alpha_perturbation_bound M hM hα
  have hc := quadratic_center_bound M k hMp hk hr
  have hp : |2 * α + α ^ 2 + β| ≤ (12 + 4 / ρ) / M := by
    calc
      _ ≤ |2 * α + α ^ 2| + |β| := abs_add_le _ _
      _ ≤ 12 / M + 4 / (ρ * M) := add_le_add ha hβ
      _ = _ := by ring
  have hdiff : t - r * ((k : ℝ) / M) ^ 2 =
      (r * ((k : ℝ) / M) ^ 2) * (2 * α + α ^ 2 + β) := by rw [ht]; ring
  have hlocal : |t - r * ((k : ℝ) / M) ^ 2| ≤ 4 * r * ((12 + 4 / ρ) / M) := by
    rw [hdiff, abs_mul, abs_of_nonneg hc.1]
    exact mul_le_mul hc.2 hp (abs_nonneg _) (by positivity)
  have hgrid := PaperP1.QuadraticIntervalGrid.scaled_center_error M k hMp r hr
  calc
    _ ≤ |t - r * ((k : ℝ) / M) ^ 2| +
        |r * ((k : ℝ) / M) ^ 2 - r * ((PaperP1.QuadraticIntervalGrid.grid M k : ℝ) / M)| :=
      abs_sub_le _ _ _
    _ ≤ 4 * r * ((12 + 4 / ρ) / M) + r / M := add_le_add hlocal hgrid
    _ = _ := by ring

end PaperP1.QuadraticRelativeError
