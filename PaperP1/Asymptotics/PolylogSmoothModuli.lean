module

public import PaperP1.Arithmetic.SmallKernelCount
public import PaperP1.Asymptotics.LogPowerExponential
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Uniform Rankin counts for smooth moduli at a polylogarithmic cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogSmoothModuli

open Finset Filter PaperP1.SmallKernelCount PaperP1.LargeOddKernel

theorem log_power_exponential (K q ε : ℝ) (hq : q < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Real.exp (K * (Real.log N) ^ q) ≤ (N : ℝ) ^ ε := by
  have hlim := (PaperP1.LogPowerExponential.log_power_ratio_tendsto q hq).const_mul K
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (by simpa only [mul_zero] using hε)))
  refine ⟨max 2 N₀, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb : K * (Real.log N) ^ q ≤ ε * Real.log N := by
    apply (div_le_iff₀ hl).mp
    simpa only [mul_div_assoc] using (hN₀ N (by omega)).le
  exact (Real.exp_le_exp.mpr hb).trans_eq (by
    rw [Real.rpow_def_of_pos hn]; congr 1; ring)

theorem odd_smooth_count (A C ε : ℝ) (hA : 2 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y X : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A → (X : ℝ) ≤ C * N * (Real.log N) ^ A →
      ∀ S : Finset ℕ,
      (∀ m ∈ S, 0 < m ∧ m ≤ X ∧ largeOddKernel Y m = 1) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) := by
  let δ := min (ε / 3) (1 / (2 * A))
  let σ := 1 - 1 / A + δ
  have hAp : 0 < A := by linarith
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδeps : δ ≤ ε / 3 := min_le_left _ _
  have hδA : δ ≤ 1 / (2 * A) := min_le_right _ _
  have hinv : 1 / A ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hA
  have hσ : 1 / 2 ≤ σ := by dsimp [σ]; linarith
  have hσp : 0 < σ := by linarith
  have hσ1 : σ < 1 := by
    have hfrac : 1 / (2 * A) = (1 / A) / 2 := by ring
    have hai : 0 < 1 / A := by positivity
    dsimp [σ]
    linarith
  have hq : A * (1 - σ) < 1 := by
    have hmul : A * (1 / A) = 1 := mul_one_div_cancel hAp.ne'
    have hAd := mul_pos hAp hδ
    dsimp [σ]
    nlinarith only [hmul, hAd]
  obtain ⟨Ne, hNe⟩ := log_power_exponential (1 / (1 - σ)) (A * (1 - σ)) (ε / 3) hq (by positivity)
  obtain ⟨Np, hNp⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow
    (C ^ σ / (1 - σ)) (A * σ) (ε / 3) (by positivity)
  refine ⟨max 2 (max Ne Np), ?_⟩
  intro N hN Y X hY hX S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsub : S ⊆ smallKernelValues Y 1 X := by
    intro m hm
    exact mem_smallKernelValues.mpr ⟨(hS m hm).1, (hS m hm).2.1, (hS m hm).2.2.le⟩
  have hcount := card_smallKernelValues_le_power Y 1 X σ hσ hσ1
  simp only [Nat.cast_one, Real.one_rpow, one_div] at hcount
  have hXpow : (X : ℝ) ^ σ ≤ (N : ℝ) ^ σ * (C ^ σ * (Real.log N) ^ (A * σ)) := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg X) hX hσp.le
    rw [Real.mul_rpow (mul_nonneg hC hn.le) (Real.rpow_nonneg hl.le _),
      Real.mul_rpow hC hn.le, ← Real.rpow_mul hl.le] at hp
    convert hp using 1; ring
  have hYpow : (Y : ℝ) ^ (1 - σ) ≤ (Real.log N) ^ (A * (1 - σ)) := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg Y) hY (by linarith : 0 ≤ 1 - σ)
    rwa [← Real.rpow_mul hl.le] at hp
  have he : Real.exp ((Y : ℝ) ^ (1 - σ) / (1 - σ)) ≤ (N : ℝ) ^ (ε / 3) := by
    apply (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hYpow (by linarith))).trans
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hNe N (by omega)
  have hp := hNp N (by omega)
  calc
    _ ≤ ((smallKernelValues Y 1 X).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ (X : ℝ) ^ σ * (1 - σ)⁻¹ * Real.exp ((Y : ℝ) ^ (1 - σ) / (1 - σ)) := hcount
    _ ≤ ((N : ℝ) ^ σ * (C ^ σ * (Real.log N) ^ (A * σ))) * (1 - σ)⁻¹ * (N : ℝ) ^ (ε / 3) := by
      gcongr
    _ = (N : ℝ) ^ σ * ((C ^ σ / (1 - σ)) * (Real.log N) ^ (A * σ)) * (N : ℝ) ^ (ε / 3) := by ring
    _ ≤ (N : ℝ) ^ σ * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) := by gcongr
    _ = (N : ℝ) ^ (σ + ε / 3 + ε / 3) := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [σ]; linarith)

end PaperP1.PolylogSmoothModuli
