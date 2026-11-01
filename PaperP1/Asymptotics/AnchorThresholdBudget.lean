module

public import PaperP1.Arithmetic.AnchorCertificateGraph
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import PaperP1.Asymptotics.ModerateCertificateAsymptotic

/-! # Actual receiver products cannot all stay below the interval threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchorThresholdBudget

open Finset Filter PaperP1.AnchorCertificateGraph

theorem threshold_power (C m t : ℕ) (E : ℝ)
    (hgap : (m : ℝ) < (t : ℝ) / 5) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      (threshold (C * N) W : ℝ) ^ m ≤ (N : ℝ) ^ ((t : ℝ) / 5) := by
  let D := 2 * E + 1
  let H := 2 * (C : ℝ) * D
  let δ := (t : ℝ) / 5 - m
  have hδ : 0 < δ := sub_pos.mpr hgap
  obtain ⟨Np, hNp⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (H ^ m) m δ hδ
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max 2 (max Np Nl), ?_⟩
  intro N hN W hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log N := hNl N (by omega)
  have hB : (2 * W + 1 : ℝ) ≤ D * Real.log N := by dsimp [D]; nlinarith only [hwidth, hlog]
  have hZ : (threshold (C * N) W : ℝ) ≤ H * N * Real.log N := by
    have hmul := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * C * N)
    dsimp [threshold]
    rw [PaperP1.BoundedIntegerMotifs.offsets_card]
    push_cast
    simpa only [H, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (threshold (C * N) W)) hZ m
  calc
    _ ≤ (H * N * Real.log N) ^ m := hpow
    _ = (N : ℝ) ^ m * (H ^ m * (Real.log N) ^ (m : ℝ)) := by
      rw [Real.rpow_natCast, mul_pow, mul_pow]
      ring
    _ ≤ (N : ℝ) ^ m * (N : ℝ) ^ δ := mul_le_mul_of_nonneg_left (hNp N (by omega)) (pow_nonneg hn.le m)
    _ = (N : ℝ) ^ ((m : ℝ) + δ) := by rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.AnchorThresholdBudget
