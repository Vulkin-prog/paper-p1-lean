module

public import PaperP1.Arithmetic.LargeKernelTuples
public import PaperP1.Asymptotics.SeveralAnchorCounts

/-! # Large-selected-kernel tuple counts and the exponent used in T1.14 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeKernelTupleCounts

open PaperP1 PaperP1.LargeKernelTuples

def beta (s : ℕ) : ℝ := (2 * (s : ℝ) - 1) / (2 * s + 1)

theorem tuple_count (m : ℕ) (C τ ε : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : ℝ, 0 < T →
        ((tuples m N (L + 1) T).card : ℝ) ≤
          (N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε) * T ^ (-1 / 2 + τ) := by
  obtain ⟨Ncount, hcount⟩ := SeveralAnchorCounts.critical_count (ι := Fin m) C τ (ε / 2) hτ hτhalf (by positivity)
  obtain ⟨Nconst, hconst⟩ := UniformReal.uniformSubpolynomialOn_le_rpow
    (ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) ((m + 1 : ℕ) : ℝ)) (ε / 2) (by positivity)
  refine ⟨max 2 (max Ncount Nconst), ?_⟩
  intro N hN L hcrit T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcoef : ((m + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (le_abs_self _).trans (hconst N (by omega) L trivial)
  have hc := hcount N (by omega) L hcrit T hT
  simp only [Fintype.card_fin] at hc
  have hcard : ((tuples m N (L + 1) T).card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) *
      (PaperP1.SeveralAnchorConfigurations.configurations (ι := Fin m) N (L + 1) T).card := by
    exact_mod_cast tuples_card m N (L + 1) T
  calc
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        ((N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε / 2) * T ^ (-1 / 2 + τ)) :=
      hcard.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
    _ = (((m + 1 : ℕ) : ℝ) * (N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε / 2)) * T ^ (-1 / 2 + τ) := by ring
    _ ≤ ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε / 2)) * T ^ (-1 / 2 + τ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem beta_bounds (s : ℕ) (hs : 2 ≤ s) : 7 / 12 < beta s ∧ beta s < 1 := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (0 : ℝ) < 2 * s + 1 := by positivity
  unfold beta
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith
  · apply (div_lt_iff₀ hden).mpr
    linarith

theorem exponent_identity (m s : ℕ) :
    (m : ℝ) + 1 / 2 - beta s / 2 = (m + 1 : ℝ) - 2 * s / (2 * s + 1) := by
  have hden : (2 * (s : ℝ) + 1) ≠ 0 := by positivity
  unfold beta
  field_simp
  ring

/-- The large-kernel branch of T1.14; its separate all-small-kernel branch is not assumed. -/
theorem large_branch (m s : ℕ) (hs : 2 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ((tuples m N (L + 1) ((N : ℝ) ^ beta s)).card : ℝ) ≤
          (N : ℝ) ^ ((m + 1 : ℝ) - 2 * s / (2 * s + 1) + ε) := by
  have hbeta : 0 < beta s := lt_trans (by norm_num) (beta_bounds s hs).1
  let τ : ℝ := min (1 / 4) (ε / (4 * beta s))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hτhalf : τ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hτbeta : beta s * τ ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * beta s)).mp (min_le_right (1 / 4) (ε / (4 * beta s)))
    change τ * (4 * beta s) ≤ ε at h
    nlinarith
  obtain ⟨N₀, hN₀⟩ := tuple_count m C τ (ε / 2) hτ hτhalf (by positivity)
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc := hN₀ N (by omega) L hcrit ((N : ℝ) ^ beta s) (Real.rpow_pos_of_pos hn _)
  calc
    _ ≤ (N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε / 2) * ((N : ℝ) ^ beta s) ^ (-1 / 2 + τ) := hc
    _ = (N : ℝ) ^ ((m : ℝ) + 1 / 2 + ε / 2 + beta s * (-1 / 2 + τ)) := by
      rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith [exponent_identity m s])

end PaperP1.LargeKernelTupleCounts
