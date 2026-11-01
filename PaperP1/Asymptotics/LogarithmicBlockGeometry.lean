module

public import PaperP1.Asymptotics.CriticalBandScale
public import Mathlib.Algebra.Order.Floor.Ring

/-! # A canonical critical length covers every fixed logarithmic block width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicBlockGeometry

def length (N : ℕ) : ℕ := ⌊Real.log N / Real.log 2⌋₊

theorem length_band (N : ℕ) (hN : 1 ≤ N) :
    |(length N : ℝ) - Real.log N / Real.log 2| ≤ 1 := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hratio : 0 ≤ Real.log N / Real.log 2 := div_nonneg hlog (Real.log_pos (by norm_num)).le
  have hlo := Nat.floor_le hratio
  have hhi := Nat.lt_floor_add_one (Real.log N / Real.log 2)
  apply abs_le.mpr
  constructor <;> dsimp [length] <;> linarith only [hlo, hhi]

theorem width_transfer (E : ℝ) (hE : 0 ≤ E) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ 1 ∧
      E * Real.log N ≤ (E / PaperP1.CriticalBandScale.lowerScale) * (length N + 1 : ℕ) := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.CriticalBandScale.critical_band_scale 1
  refine ⟨max 2 N₀, ?_⟩
  intro N hN
  have hband := length_band N (by omega)
  refine ⟨hband, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hN₀ N (by omega) (length N) hband).1
    (div_nonneg hE PaperP1.CriticalBandScale.lowerScale_pos.le)
  have heq : (E / PaperP1.CriticalBandScale.lowerScale) *
      (PaperP1.CriticalBandScale.lowerScale * Real.log N) = E * Real.log N := by
    field_simp [PaperP1.CriticalBandScale.lowerScale_pos.ne']
  rwa [heq] at hmul

end PaperP1.LogarithmicBlockGeometry
