module

public import PaperP1.Asymptotics.ComparableSplitProductCount
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Actual value heights control centres of nonempty logarithmic-width blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BlockCentreHeights

def lower (a : ℝ) : ℝ := min (a / 2) 1

def upper (b : ℝ) : ℝ := max (b + 1) 1

theorem lower_pos (a : ℝ) (ha : 0 < a) : 0 < lower a := by
  dsimp [lower]
  positivity

theorem default_bounds (a b : ℝ) (N : ℕ) :
    lower a * N ≤ N ∧ (N : ℝ) ≤ upper b * N := by
  constructor
  · simpa only [one_mul, lower] using mul_le_mul_of_nonneg_right (min_le_right (a / 2) 1) (Nat.cast_nonneg N)
  · simpa only [one_mul, upper] using mul_le_mul_of_nonneg_right (le_max_right (b + 1) 1) (Nat.cast_nonneg N)

theorem centre_bounds (a b : ℝ) (N W x v : ℕ)
    (hv : a * N ≤ v ∧ (v : ℝ) ≤ b * N) (hdistance : ((v : ℤ) - x).natAbs ≤ W)
    (hWlo : (W : ℝ) ≤ (a / 2) * N) (hWhi : (W : ℝ) ≤ N) :
    lower a * N ≤ x ∧ (x : ℝ) ≤ upper b * N := by
  have hInt : |(v : ℤ) - x| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hdistance
  have hReal : |(v : ℝ) - x| ≤ W := by exact_mod_cast hInt
  have habs := abs_le.mp hReal
  have hlo : (a / 2) * N ≤ (x : ℝ) := by nlinarith only [hv.1, habs.2, hWlo]
  have hhi : (x : ℝ) ≤ (b + 1) * N := by nlinarith only [hv.2, habs.1, hWhi]
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_left (a / 2) 1) (Nat.cast_nonneg N)).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right (le_max_left (b + 1) 1) (Nat.cast_nonneg N))⟩

theorem logarithmic_radius (a E : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      (W : ℝ) ≤ (a / 2) * N ∧ (W : ℝ) ≤ N := by
  obtain ⟨N₁, hN₁⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * E / a) 1 1 (by norm_num)
  obtain ⟨N₂, hN₂⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow E 1 1 (by norm_num)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN W hW
  have h₁ := hN₁ N (by omega)
  have h₂ := hN₂ N (by omega)
  simp only [Real.rpow_one] at h₁ h₂
  have hmul := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ a / 2)
  have heq : (a / 2) * ((2 * E / a) * Real.log N) = E * Real.log N := by field_simp
  rw [heq] at hmul
  exact ⟨hW.trans hmul, hW.trans h₂⟩

def radius (D : ℝ) (L : ℕ) : ℕ := ⌈D * (L + 1 : ℕ)⌉₊ + 1

theorem radius_pos (D : ℝ) (L : ℕ) : 0 < radius D L := by dsimp [radius]; omega

theorem distance_le_radius (D : ℝ) (L d : ℕ) (hd : (d : ℝ) ≤ D * (L + 1 : ℕ)) : d ≤ radius D L := by
  have hceil : (d : ℝ) ≤ (⌈D * (L + 1 : ℕ)⌉₊ : ℝ) := hd.trans (Nat.le_ceil _)
  have hnat : d ≤ ⌈D * (L + 1 : ℕ)⌉₊ := by exact_mod_cast hceil
  dsimp [radius]
  omega

theorem radius_logarithmic (D Cband : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (radius D L : ℝ) ≤ (D * PaperP1.CriticalBandScale.upperScale + 2) * Real.log N := by
  obtain ⟨NB, hNB⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max NB NL, ?_⟩
  intro N hN L hband
  have hlog : 1 ≤ Real.log N := hNL N (by omega)
  have hDB : D * (L + 1 : ℕ) ≤ (D * PaperP1.CriticalBandScale.upperScale) * Real.log N := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hNB N (by omega) L hband).2 hD
  have hceil : (⌈D * (L + 1 : ℕ)⌉₊ : ℝ) < D * (L + 1 : ℕ) + 1 := Nat.ceil_lt_add_one (by positivity)
  dsimp [radius]
  push_cast at hceil hDB ⊢
  nlinarith only [hceil, hDB, hlog]

end PaperP1.BlockCentreHeights
