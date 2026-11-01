module

public import PaperP1.Arithmetic.CodedClassTargets
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Arithmetic.SmoothSupportBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Uniform position and coefficient budgets for two-class target codes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassCodeBudget

open Finset PaperP1.CriticalBandScale

def primorialExponent : ℕ := ⌈(2 * upperScale) * Real.log 4⌉₊

theorem primorial_height {N L : ℕ} (hN : 1 ≤ N)
    (hB : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N) :
    primorial (2 * (L + 1)) ≤ N ^ primorialExponent := by
  apply (primorial_le_four_pow _).trans
  apply PaperP1.SmoothSupportBounds.four_pow_cutoff_le_polynomial hN
    (D := 2 * upperScale)
  · have h := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h
  · exact Nat.le_ceil _

theorem coefficient_count (K : ℕ) (C θ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ m : ℕ, m ≤ N ^ (2 * K) →
        ((ClassCoefficientValues.values (2 * (L + 1)) m ⌊(N : ℝ) ^ θ⌋₊).card : ℝ) ≤
          (N : ℝ) ^ (θ + ε) := by
  obtain ⟨Np, hNp⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually primorialExponent (ε / 2) (by positivity)
  obtain ⟨Nm, hNm⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (2 * K) (ε / 2) (by positivity)
  obtain ⟨NG, hNG⟩ := critical_band_scale C
  refine ⟨max Np (max Nm (max NG 1)), ?_⟩
  intro N hN L hband m hm
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hNG N (by omega) L hband).2
  have hp := hNp N (by omega) _ (primorial_height hN1 hB)
  have hdiv := hNm N (by omega) m hm
  have he : (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le (Real.rpow_nonneg hNr.le θ)
  have hfinite : ((ClassCoefficientValues.values (2 * (L + 1)) m ⌊(N : ℝ) ^ θ⌋₊).card : ℝ) ≤
      ((primorial (2 * (L + 1))).divisors.card : ℝ) * (m.divisors.card : ℝ) * ⌊(N : ℝ) ^ θ⌋₊ := by
    exact_mod_cast ClassCoefficientValues.card_values (2 * (L + 1)) m ⌊(N : ℝ) ^ θ⌋₊
  calc
    _ ≤ _ := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ θ :=
      mul_le_mul (mul_le_mul hp hdiv (Nat.cast_nonneg _) (Real.rpow_nonneg hNr.le _)) he
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]; congr 1; ring

theorem position_count (s K : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((CodedClassTargets.pool s L K).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A : ℕ := (K + 1) * (s + 2) ^ K
  obtain ⟨NP, hNP⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le A K ε hε
  obtain ⟨NG, hNG⟩ := critical_band_scale C
  refine ⟨max NP NG, ?_⟩
  intro N hN L hband
  have hbase : (s + 1) * (L + 1) + 1 ≤ (s + 2) * (L + 1) := by nlinarith
  have hpool : (CodedClassTargets.pool s L K).card ≤ A * (L + 1) ^ K := by
    calc
      _ ≤ (K + 1) * ((s + 1) * (L + 1) + 1) ^ K := CodedClassTargets.card_pool s L K
      _ ≤ (K + 1) * ((s + 2) * (L + 1)) ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase K)
      _ = _ := by simp only [mul_pow, A, mul_assoc]
  have hpoly := hNP N (by omega) L (hNG N (by omega) L hband).2
  calc
    _ ≤ ((A * (L + 1) ^ K : ℕ) : ℝ) := by exact_mod_cast hpool
    _ = (A : ℝ) * (L + 1 : ℝ) ^ K := by push_cast; rfl
    _ ≤ _ := (le_abs_self _).trans hpoly

end PaperP1.ClassCodeBudget
