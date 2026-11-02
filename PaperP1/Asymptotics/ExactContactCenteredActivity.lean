module

public import PaperP1.Model.ExactContactCentered
public import PaperP1.Asymptotics.ExactContactActivation

/-! # The total exact-contact covariance is only N^(-2+epsilon), without BCN -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactContactCenteredActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ExactContactEdges

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (edges N L) ≤ (N : ℝ) ^ (-2 + ε) := by
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let Kp := 2 * (2 : ℝ) ^ C
  let Kq := ((2 : ℝ) ^ C) ^ 2
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NI, hi⟩ := RegularStarts.card_irregularStarts_le_rpow_eventually
    (2 * CriticalBandScale.upperScale) (mul_nonneg (by norm_num) CriticalBandScale.upperScale_pos.le) δ hδ
  obtain ⟨NQ, hq⟩ := ContactSeedMass.point_bound C δ hδ
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (Kq + Kp ^ 2) (-2 + 2 * δ) δ hδ
  refine ⟨max 2 (max NS (max NI (max NQ (max NP (max NG NF))))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hB := (hs N (by omega) L hband).2
  have hdouble : ((2 * L + 1 : ℕ) : ℝ) ≤ (2 * CriticalBandScale.upperScale) * Real.log N := by
    have htw : ((2 * L + 1 : ℕ) : ℝ) ≤ 2 * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 * L + 1 ≤ 2 * (L + 1) by omega)
    nlinarith only [htw, hB]
  have hcount := hi N (by omega) (2 * L) hdouble
  have hpoint (x : ℕ) (hx : x ∈ starts N L) : infiniteJointMoment L {x, x + L} ≤ Kq * (N : ℝ) ^ (-2 + δ) := by
    simpa only [ContactFamilySeeds.prescribed_contact L hL, Kq] using
      hq N (by omega) L hband (fun _ ↦ Affine.startRhs L) x (mem_filter.mp hx).1
  have hfinite := ExactContactCentered.absolute_bound (by omega : 2 ≤ N) hL (Kp / N)
    (Kq * (N : ℝ) ^ (-2 + δ)) (by dsimp [Kp]; positivity) (by dsimp [Kq]; positivity)
    (fun x hx ↦ hp N (by omega) L hband x hx) hpoint
  have hpsq : (Kp / N) ^ 2 ≤ Kp ^ 2 * (N : ℝ) ^ (-2 + δ) := by
    calc
      _ = Kp ^ 2 * (N : ℝ) ^ (-2 : ℝ) := by rw [div_pow, Real.rpow_neg hn.le, Real.rpow_two, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])) (sq_nonneg Kp)
  calc
    _ ≤ ((RegularStarts.irregularStarts N (2 * L)).card : ℝ) * (Kq * (N : ℝ) ^ (-2 + δ) + (Kp / N) ^ 2) := hfinite
    _ ≤ (N : ℝ) ^ δ * ((Kq + Kp ^ 2) * (N : ℝ) ^ (-2 + δ)) := by
      apply mul_le_mul hcount _ (by positivity) (Real.rpow_nonneg hn.le _)
      nlinarith only [hpsq]
    _ = (Kq + Kp ^ 2) * (N : ℝ) ^ (-2 + 2 * δ) := by rw [mul_comm ((N : ℝ) ^ δ), mul_assoc, ← Real.rpow_add hn]; congr 2; ring
    _ ≤ (N : ℝ) ^ ((-2 + 2 * δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.ExactContactCenteredActivity
