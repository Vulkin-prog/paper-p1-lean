module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Arithmetic.PolynomialEndpointBudget

/-! # Every fixed polynomial in a critical window is smaller than its dyadic scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalPolynomialScale

open Filter PaperP1.CriticalBandScale

theorem polynomial_lt_scale (C M : ℝ) (hM : 0 ≤ M) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      M * ((L + 1 : ℕ) : ℝ) ^ k < (N : ℝ) := by
  have hbase : Tendsto (fun N : ℕ ↦ (Real.log N) ^ k / N) atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun N : ℕ ↦ M * upperScale ^ k * (Real.log N) ^ k / N) atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_const_nhds.mul hbase : Tendsto (fun N : ℕ ↦ (M * upperScale ^ k) * ((Real.log N) ^ k / N)) atTop (nhds ((M * upperScale ^ k) * 0)))
  obtain ⟨Ncore, hcore⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 1 (by norm_num))
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  refine ⟨max Ncore (max Nscale 2), ?_⟩
  intro N hN L hcrit
  have hNtwo : 2 ≤ N := (le_max_right Nscale 2).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hscale N ((le_max_left Nscale 2).trans ((le_max_right _ _).trans hN)) L hcrit).2
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (L + 1)) hB k
  have hlt := (div_lt_one hNpos).mp (hcore N ((le_max_left _ _).trans hN))
  calc
    _ ≤ M * (upperScale * Real.log N) ^ k := mul_le_mul_of_nonneg_left hpower hM
    _ = M * upperScale ^ k * (Real.log N) ^ k := by rw [mul_pow]; ring
    _ < N := hlt

theorem source_size_eventually (C : ℝ) (a J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ (L + 1) ^ J →
      a * (2 * H * ((L + 1) + 1)) + (L + 1) < N := by
  obtain ⟨Ncore, hcore⟩ := polynomial_lt_scale C ((4 * a + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) (J + 1)
  refine ⟨Ncore, ?_⟩
  intro N hN L H hcrit hH
  have hlarge : (4 * a + 1) * (L + 1) ^ (J + 1) < N := by exact_mod_cast hcore N hN L hcrit
  exact (PolynomialEndpointBudget.source_size_bound (by omega : 1 ≤ L + 1) hH).trans_lt hlarge

end PaperP1.CriticalPolynomialScale
