module

public import PaperP1.Asymptotics.RoundedScaleLower

/-! # Explicit square-root and side-cost budgets for the literal rounded determinant scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RoundedScaleSideBudget

open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale

theorem rounded_upper {N : ℕ} (hN : 2 ≤ N) {D E U V ζ : ℝ}
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hU : 1 ≤ U) (hV : 1 ≤ V) (hζ : 0 ≤ ζ) :
    (horizontalScale N D E U V ζ : ℝ) ≤ 2 * (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hn1 hζ
  have he : 1 ≤ Real.exp (logShape N D E U V) := by
    have hh := Real.exp_le_exp.mpr (RoundedScaleLower.shape_nonnegative hN hD hE hU hV)
    simpa only [Real.exp_zero] using hh
  have hbase : 1 ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) := by
    calc
      _ ≤ (N : ℝ) ^ ζ := hp
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (N : ℝ) ^ ζ)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) by positivity)).le
  change (horizontalScale N D E U V ζ : ℝ) ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) + 1 at hceil
  linarith only [hceil, hbase]

theorem square_root_bound (N M : ℕ) (ζ S W : ℝ) (hS : 0 ≤ S) (hW : 0 ≤ W)
    (hM : (M : ℝ) ≤ 2 * (N : ℝ) ^ ζ * S) :
    Real.sqrt (W * M) ≤ 2 * (N : ℝ) ^ (ζ / 2) * Real.sqrt (W * S) := by
  have hp : ((N : ℝ) ^ (ζ / 2)) ^ 2 = (N : ℝ) ^ ζ := by
    simpa only [Nat.cast_ofNat, show ζ / 2 * 2 = ζ by ring] using
      (Real.rpow_mul_natCast (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (ζ / 2) 2).symm
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (mul_nonneg hW (Nat.cast_nonneg M))]
  simp only [mul_pow, hp, Real.sq_sqrt (mul_nonneg hW hS)]
  have hb := mul_le_mul_of_nonneg_left hM hW
  have hn : 0 ≤ (N : ℝ) ^ ζ * (W * S) := by positivity
  nlinarith only [hb, hn]

theorem horizontal_cost (N M : ℕ) (hN : 1 ≤ N) {D E S η ζ : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hS : 0 ≤ S) (hη : 0 ≤ η) (hζ : 0 ≤ ζ)
    (hM : (M : ℝ) ≤ 2 * (N : ℝ) ^ ζ * S) :
    60 * (N : ℝ) ^ η * Real.sqrt (D * E * M) + 32 * E + 8 * D ≤
      160 * (N : ℝ) ^ (η + ζ / 2) * (Real.sqrt (D * E * S) + D + E) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := square_root_bound N M ζ S (D * E) hS (mul_nonneg hD hE) hM
  have hadd : (N : ℝ) ^ η * (N : ℝ) ^ (ζ / 2) = (N : ℝ) ^ (η + ζ / 2) := (Real.rpow_add hn _ _).symm
  have hq : 1 ≤ (N : ℝ) ^ (η + ζ / 2) := Real.one_le_rpow hn1 (by positivity)
  calc
    _ ≤ 60 * (N : ℝ) ^ η * (2 * (N : ℝ) ^ (ζ / 2) * Real.sqrt (D * E * S)) + 32 * E + 8 * D := by gcongr
    _ = 120 * (N : ℝ) ^ (η + ζ / 2) * Real.sqrt (D * E * S) + 32 * E + 8 * D := by
      rw [show 60 * (N : ℝ) ^ η * (2 * (N : ℝ) ^ (ζ / 2) * Real.sqrt (D * E * S)) =
        120 * ((N : ℝ) ^ η * (N : ℝ) ^ (ζ / 2)) * Real.sqrt (D * E * S) by ring, hadd]
    _ ≤ _ := by
      have hd := mul_nonneg (sub_nonneg.mpr hq) hD
      have he := mul_nonneg (sub_nonneg.mpr hq) hE
      have ht := mul_nonneg (show 0 ≤ (N : ℝ) ^ (η + ζ / 2) by positivity) (Real.sqrt_nonneg (D * E * S))
      nlinarith only [hd, he, ht, hD, hE]

theorem vertical_cost (N M : ℕ) (hN : 1 ≤ N) {U V S η ζ K : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hS : 0 ≤ S) (hK : 0 ≤ K) (hζ : 0 ≤ ζ)
    (hM : (M : ℝ) ≤ 2 * (N : ℝ) ^ ζ * S) :
    K * (N : ℝ) ^ η * (Real.sqrt (U * V * M) + U + V) ≤
      (2 * K) * (N : ℝ) ^ (η + ζ / 2) * (Real.sqrt (U * V * S) + U + V) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := square_root_bound N M ζ S (U * V) hS (mul_nonneg hU hV) hM
  have hb : 1 ≤ (N : ℝ) ^ (ζ / 2) := Real.one_le_rpow hn1 (by positivity)
  have hadd : (N : ℝ) ^ η * (N : ℝ) ^ (ζ / 2) = (N : ℝ) ^ (η + ζ / 2) := (Real.rpow_add hn _ _).symm
  calc
    _ ≤ K * (N : ℝ) ^ η * ((N : ℝ) ^ (ζ / 2) * (2 * Real.sqrt (U * V * S) + U + V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hu := mul_nonneg (sub_nonneg.mpr hb) hU
      have hv := mul_nonneg (sub_nonneg.mpr hb) hV
      nlinarith only [hs, hu, hv]
    _ = K * (N : ℝ) ^ (η + ζ / 2) * (2 * Real.sqrt (U * V * S) + U + V) := by rw [← mul_assoc, mul_assoc K, hadd]
    _ ≤ _ := by
      have hu := mul_nonneg (show 0 ≤ K * (N : ℝ) ^ (η + ζ / 2) by positivity) hU
      have hv := mul_nonneg (show 0 ≤ K * (N : ℝ) ^ (η + ζ / 2) by positivity) hV
      nlinarith only [hu, hv]

end PaperP1.RoundedScaleSideBudget
