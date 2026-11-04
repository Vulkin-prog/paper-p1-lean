module

public import PaperP1.Asymptotics.HomogeneousChannelMass

/-! # Fixed changes of dyadic scale for original private-pair probabilities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalScaledChannelPowers

open Finset PaperP1.Model PaperP1.HomogeneousRunMass PaperP1.CriticalChannelPowers

def band (C : ℝ) (d : ℕ) : ℝ := C + |Real.log d / Real.log 2|

theorem critical_band_mul {N L d : ℕ} {C : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    |(L : ℝ) - Real.log (d * N : ℕ) / Real.log 2| ≤ band C d := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_mul, Real.log_mul hd' hn, add_div]
  calc
    _ = |((L : ℝ) - Real.log N / Real.log 2) - Real.log d / Real.log 2| := by congr 1; ring
    _ ≤ |(L : ℝ) - Real.log N / Real.log 2| + |Real.log d / Real.log 2| := abs_sub _ _
    _ ≤ _ := add_le_add hcrit le_rfl

theorem uniform_pair (a b d : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hd : 0 < d) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e ∈ PrivateChannelActivity.pairs N H a b L,
        probability L e ≤ ((d * N : ℕ) : ℝ) ^ (-5 / 3 + ε) := by
  let P := ((2 : ℝ) ^ band C d) ^ 2 * (2 : ℝ) ^ ((band C d + 1) / b)
  obtain ⟨Ng, hg⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Na, ha'⟩ := HalfCountSchedule.factor_absorption P (-5 / 3) ε hε
  refine ⟨max 2 (max Ng Na), by omega, ?_⟩
  intro N hN L H hcrit e he
  have hscale : N ≤ d * N := by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ d by omega)
  have hn : (0 : ℝ) < (d * N : ℕ) := by exact_mod_cast (show 0 < d * N by omega)
  have hn1 : (1 : ℝ) ≤ (d * N : ℕ) := by exact_mod_cast (show 1 ≤ d * N by omega)
  have hband := critical_band_mul (by omega : 0 < N) hd hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using hg N (by omega) L hcrit
  have hpoint := HomogeneousChannelMass.finite_pair_bound (by omega : 2 ≤ N) ha hab hcop hlarge he
  have hfrac : (1 : ℝ) / b ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
    exact_mod_cast hb
  calc
    _ ≤ (((2 : ℝ) ^ band C d) ^ 2 * ((d * N : ℕ) : ℝ) ^ (-2 : ℝ)) *
        ((2 : ℝ) ^ ((band C d + 1) / b) * ((d * N : ℕ) : ℝ) ^ (1 / (b : ℝ))) :=
      hpoint.trans (mul_le_mul (nominal_square_upper (by omega) hband)
        (window_root_upper (by omega) (ha.trans hab) hband) (by positivity) (by positivity))
    _ = P * ((d * N : ℕ) : ℝ) ^ (-2 + 1 / (b : ℝ)) := by
      rw [Real.rpow_add hn]
      dsimp only [P]
      ring
    _ ≤ P * ((d * N : ℕ) : ℝ) ^ (-5 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hfrac])) (by positivity)
    _ ≤ _ := ha' (d * N) (by omega)

end PaperP1.CriticalScaledChannelPowers
