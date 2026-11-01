module

public import PaperP1.Asymptotics.LogSquaredPrimePool

/-! # The full conditional pool term at a fixed fractional length threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalPoolTerm

open Finset PaperP1.Arithmetic PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget
  PaperP1.WindowPoolCount PaperP1.CriticalBandScale PaperP1.LogSquaredPrimePool

def term (N L T : ℕ) (A : Finset ℕ) : ℝ :=
  (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (T - 1) * (L + 1) * (poolValues (rawValues A L) (L + 1) (3 * N)).card

theorem binary_factor_bound {N L T : ℕ} {C δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (hT : (T : ℝ) ≤ (1 - δ) * L) :
    (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (T - 1) ≤
      Real.exp (δ * C * Real.log 2) * (N : ℝ) ^ (-δ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlog : Real.log N - C * Real.log 2 ≤ (L : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hband).1 hlogTwo.le
    rw [sub_mul, div_mul_cancel₀ _ hlogTwo.ne'] at h
    linarith
  have hTminus : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.sub_le T 1
  have hTlog := mul_le_mul_of_nonneg_right (hTminus.trans hT) hlogTwo.le
  have hδlog := mul_le_mul_of_nonneg_left hLlog hδ
  have hexponent : (((T - 1 : ℕ) : ℝ) - L) * Real.log 2 ≤
      δ * C * Real.log 2 + Real.log N * (-δ) := by nlinarith
  calc
    _ = Real.exp ((((T - 1 : ℕ) : ℝ) - L) * Real.log 2) := by
      rw [sub_mul, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ Real.exp (δ * C * Real.log 2 + Real.log N * (-δ)) := Real.exp_le_exp.mpr hexponent
    _ = _ := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]

theorem term_le_power_critical (C : ℝ) (j : ℕ) (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ T : ℕ, (T : ℝ) ≤ (1 - δ) * L → ∀ A : Finset ℕ,
        A ⊆ Model.dyadicBlock N → A.card ≤ j → term N L T A ≤ (N : ℝ) ^ (1 / 2 - δ + ε) := by
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨Npool, hNpool, hpool⟩ := actual_pool_count_critical C j η hη
  obtain ⟨Nwidth, hwidth⟩ := critical_band_scale C
  obtain ⟨NB, hB⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 η hη
  obtain ⟨NC, hC⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (Real.exp (δ * C * Real.log 2)) 0 η hη
  refine ⟨max Npool (max Nwidth (max NB NC)), by omega, ?_⟩
  intro N hN L hband T hT A hA hj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfinite := binary_factor_bound (by omega : 0 < N) hδ hband hT
  have hpoolN := hpool N (by omega) L hband A hA hj
  have hwidthN := (hwidth N (by omega) L hband).2
  have hBN : (L + 1 : ℝ) ≤ (N : ℝ) ^ η := by
    simpa only [one_mul, pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hB N (by omega) L hwidthN
  have hCN : Real.exp (δ * C * Real.log 2) ≤ (N : ℝ) ^ η := by
    simpa only [pow_zero, mul_one, abs_of_pos (Real.exp_pos _)] using hC N (by omega) L hwidthN
  calc
    term N L T A ≤ (Real.exp (δ * C * Real.log 2) * (N : ℝ) ^ (-δ)) * (L + 1) *
        (poolValues (rawValues A L) (L + 1) (3 * N)).card := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfinite (by positivity)) (Nat.cast_nonneg _)
    _ ≤ ((N : ℝ) ^ η * (N : ℝ) ^ (-δ)) * (N : ℝ) ^ η * (N : ℝ) ^ (1 / 2 + η) := by
      gcongr
    _ = _ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      dsimp [η]
      ring

theorem floor_threshold_le (L : ℕ) (δ : ℝ) (hδ : δ ≤ 1) :
    ((⌊(1 - δ) * (L : ℝ)⌋₊ : ℕ) : ℝ) ≤ (1 - δ) * L :=
  Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg L))

theorem fractional_term_le_power_critical (C : ℝ) (j : ℕ) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ Model.dyadicBlock N → A.card ≤ j →
        term N L ⌊(1 - δ) * (L : ℝ)⌋₊ A ≤ (N : ℝ) ^ (1 / 2 - δ + ε) := by
  obtain ⟨N₀, hN₀, hbound⟩ := term_le_power_critical C j δ ε hδ.le hε
  exact ⟨N₀, hN₀, fun N hN L hband A hA hj ↦
    hbound N hN L hband _ (floor_threshold_le L δ hδ1.le) A hA hj⟩

end PaperP1.ConditionalPoolTerm
