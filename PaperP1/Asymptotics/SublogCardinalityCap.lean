module

public import PaperP1.Asymptotics.CriticalBandScale

/-! # A sublogarithmic cardinality schedule is uniformly small at every critical length -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SublogCardinalityCap

open Filter PaperP1.CriticalBandScale

theorem uniform_cap (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (C a : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (K N : ℝ) ≤ a * L := by
  have hconstant : (0 : ℝ) < a * lowerScale / 2 :=
    div_pos (mul_pos ha lowerScale_pos) (by norm_num)
  obtain ⟨NK, hk⟩ := eventually_atTop.mp
    (hK.eventually (eventually_lt_nhds hconstant))
  obtain ⟨NS, hs⟩ := critical_band_scale C
  obtain ⟨NL, hl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop (2 / lowerScale)))
  refine ⟨2 + NK + NS + NL, by omega, ?_⟩
  intro N hN L hband
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall := (div_lt_iff₀ hlog).mp (hk N (by omega))
  have hlower : lowerScale * Real.log N ≤ (L : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using (hs N (by omega) L hband).1
  have htwo : 2 ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp (hl N (by omega))
    nlinarith only [h]
  have hL : (1 : ℝ) ≤ L := by linarith only [htwo, hlower]
  have hscaled := mul_le_mul_of_nonneg_left hlower ha.le
  have hLscaled : a ≤ a * L := by nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hL)]
  nlinarith only [hsmall, hscaled, hLscaled]

end PaperP1.SublogCardinalityCap
