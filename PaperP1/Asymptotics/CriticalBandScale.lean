module

public import PaperP1.Arithmetic.PrimeLogBudget

/-! # Uniform logarithmic scales for every length in a critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalBandScale

open Filter

def lowerScale : ℝ := 1 / (2 * Real.log 2)

def upperScale : ℝ := 1 / Real.log 2 + 1

theorem lowerScale_pos : 0 < lowerScale := by
  unfold lowerScale
  exact div_pos zero_lt_one (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem upperScale_pos : 0 < upperScale := by
  unfold upperScale
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem critical_band_scale (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        lowerScale * Real.log N ≤ ((L + 1 : ℕ) : ℝ) ∧
          ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop (max (C + 1) ((C + 1) / lowerScale))))
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  have hlarge := hN₀ N hN
  have hconstant : C + 1 ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp ((le_max_right _ _).trans hlarge)
    nlinarith
  have hconstant' : C + 1 ≤ Real.log N := (le_max_left _ _).trans hlarge
  have hlog : Real.log N / Real.log 2 = (2 * lowerScale) * Real.log N := by
    unfold lowerScale
    ring
  have hbounds := abs_le.mp hband
  rw [hlog] at hbounds
  have hu : upperScale = 2 * lowerScale + 1 := by
    unfold lowerScale upperScale
    ring
  rw [hu]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

end PaperP1.CriticalBandScale
