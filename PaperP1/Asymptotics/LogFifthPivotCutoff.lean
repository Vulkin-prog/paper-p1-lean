module

public import PaperP1.Analysis.ElementaryLogGrowth
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.GCongr

/-! # Uniform collision absorption at the actual natural log-fifth cutoff

The floor is retained exactly. The threshold precedes every moving
maximal width, and no fixed offset from a critical length is imposed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogFifthPivotCutoff

def cutoff (N : ℕ) : ℕ := ⌊(Real.log N) ^ 5⌋₊

theorem cutoff_upper (N : ℕ) (hN : 1 ≤ N) :
    (cutoff N : ℝ) ≤ (Real.log N) ^ 5 := by
  exact Nat.floor_le (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)

theorem quadratic_absorption (D η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, (B : ℝ) ≤ D * Real.log N →
      (B : ℝ) ^ 2 + 2 ≤ η * (cutoff N : ℝ) := by
  obtain ⟨NL, hL⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually
    (max 2 (2 * (D ^ 2 + 2) / η))
  refine ⟨NL, ?_⟩
  intro N hN B hB
  let H := Real.log (N : ℝ)
  have htwo : 2 ≤ H := (le_max_left _ _).trans (hL N hN).1
  have hlarge : 2 * (D ^ 2 + 2) / η ≤ H := (le_max_right _ _).trans (hL N hN).1
  have hH : 0 ≤ H := by linarith
  have hs : 1 ≤ H ^ 2 := by nlinarith only [htwo, sq_nonneg (H - 1)]
  have hcube : H ≤ H ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hs hH]
  have hcoeff : D ^ 2 + 2 ≤ η * H ^ 3 / 2 := by
    have ha := (div_le_iff₀ hη).mp hlarge
    have hb := mul_le_mul_of_nonneg_left hcube hη.le
    linarith only [ha, hb]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 5
  norm_num at hp
  have hf : H ^ 5 / 2 ≤ (cutoff N : ℝ) := by
    have hfl := Nat.lt_floor_add_one (H ^ 5)
    change H ^ 5 < (cutoff N : ℝ) + 1 at hfl
    linarith only [hfl, hp]
  have hbs := pow_le_pow_left₀ (Nat.cast_nonneg B) hB 2
  rw [mul_pow] at hbs
  calc
    (B : ℝ) ^ 2 + 2 ≤ (D ^ 2 + 2) * H ^ 2 := by
      change (B : ℝ) ^ 2 ≤ D ^ 2 * H ^ 2 at hbs
      nlinarith only [hbs, hs]
    _ ≤ (η * H ^ 3 / 2) * H ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg H)
    _ = η * (H ^ 5 / 2) := by ring
    _ ≤ η * (cutoff N : ℝ) := mul_le_mul_of_nonneg_left hf hη.le

theorem uniform_data (D t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B K : ℕ, (B : ℝ) ≤ D * Real.log N → K + 1 ≤ B →
      2 * B ≤ cutoff N ∧ 1 ≤ cutoff N ∧
      ((K : ℝ) * (K + 1 : ℕ) + 1) / cutoff N ≤ t ∧
      ((K : ℝ) * (K + 1 : ℕ) + 1) ≤ cutoff N ∧
      (cutoff N : ℝ) ≤ (Real.log N) ^ 5 := by
  obtain ⟨NC, hC⟩ := quadratic_absorption D t ht
  refine ⟨NC, ?_⟩
  intro N hN B K hB hKB
  have hquad := hC N (by omega) B hB
  have hsmall : t * (cutoff N : ℝ) ≤ cutoff N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg (cutoff N))
  have hbig := hquad.trans hsmall
  have htwoB : 2 * B ≤ cutoff N := by
    have hh : (2 : ℝ) * B ≤ cutoff N := by nlinarith only [hbig, sq_nonneg ((B : ℝ) - 1)]
    exact_mod_cast hh
  have hz : (0 : ℝ) < cutoff N := by exact_mod_cast (show 0 < cutoff N by omega)
  have hk : (K : ℝ) ≤ B := by exact_mod_cast (show K ≤ B by omega)
  have hk1 : ((K + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast hKB
  have hprod := mul_le_mul hk hk1 (Nat.cast_nonneg (K + 1)) (Nat.cast_nonneg B)
  have hc : ((K : ℝ) * (K + 1 : ℕ) + 1) ≤ (B : ℝ) ^ 2 + 2 := by nlinarith only [hprod]
  refine ⟨htwoB, by omega, (div_le_iff₀ hz).mpr (hc.trans hquad),
    hc.trans hbig, cutoff_upper N (by omega)⟩

end PaperP1.LogFifthPivotCutoff
