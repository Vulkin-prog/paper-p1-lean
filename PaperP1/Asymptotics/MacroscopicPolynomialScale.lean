module

public import PaperP1.Asymptotics.MacroscopicIntervalGeometry
public import PaperP1.Arithmetic.PolynomialEndpointBudget

/-! # Every fixed critical-window polynomial is below every macroscopic source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicPolynomialScale

open Filter PaperP1.CriticalBandScale PaperP1.MacroscopicIntervalGeometry

theorem polynomial_lt_source (C δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      ∀ x ∈ starts M δ, A * ((L + 1 : ℕ) : ℝ) ^ k < x := by
  have hbase : Tendsto (fun M : ℕ ↦ (Real.log M) ^ k / (M : ℝ) ^ δ) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (PaperP1.PNT.tendsto_pow_log_div_pow_atTop δ (k : ℝ) hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun M : ℕ ↦ A * upperScale ^ k * (Real.log M) ^ k / (M : ℝ) ^ δ)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_const_nhds.mul hbase : Tendsto
        (fun M : ℕ ↦ (A * upperScale ^ k) * ((Real.log M) ^ k / (M : ℝ) ^ δ))
        atTop (nhds ((A * upperScale ^ k) * 0)))
  obtain ⟨MC, hC⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 1 (by norm_num))
  obtain ⟨MB, hB⟩ := critical_band_scale C
  refine ⟨max MC MB, ?_⟩
  intro M hM L hcrit x hx
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hwidth := (hB M (by omega) L hcrit).2
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (L + 1)) hwidth k
  have hsmall := (div_lt_one (Real.rpow_pos_of_pos hm δ)).mp (hC M (by omega))
  calc
    _ ≤ A * (upperScale * Real.log M) ^ k := mul_le_mul_of_nonneg_left hp hA
    _ = A * upperScale ^ k * (Real.log M) ^ k := by rw [mul_pow]; ring
    _ < (M : ℝ) ^ δ := hsmall
    _ ≤ x := (mem_starts_iff.mp hx).1

end PaperP1.MacroscopicPolynomialScale
