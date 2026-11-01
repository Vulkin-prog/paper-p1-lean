module

public import PaperP1.Arithmetic.LargeAnchorPairs
public import PaperP1.Arithmetic.SmallKernelWindows
public import PaperP1.Asymptotics.LogPowerExponential
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Uniform asymptotic counts for the actual selected-kernel families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedKernelCounts

open PaperP1 PaperP1.CriticalBandScale PaperP1.ExpSqrtLog
open PaperP1.LargeAnchorPairs PaperP1.SmallKernelWindows

def smallFactor (B : ℕ) : ℝ := 2 * Real.sqrt 3 * (B + 1) * Real.exp (2 * Real.sqrt B)

def largeFactor (τ : ℝ) (B : ℕ) : ℝ :=
  8 * Real.sqrt 3 * (B + 1) * Real.exp (2 * Real.sqrt B) *
    Real.exp (PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ))

theorem small_factor_subpolynomial (D : ℝ) (hD : 0 ≤ D) :
    UniformSubpolynomialOn (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ smallFactor B) := by
  have hlin := uniformSubpolynomialOn_linear_log_add_one
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) D hD (fun _ _ h ↦ h)
  have hsqrt := uniformSubpolynomialOn_exp_sqrt_of_le_log
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) 2 D (by norm_num) hD (fun _ _ h ↦ h)
  simpa only [smallFactor, mul_assoc] using
    uniformSubpolynomialOn_const_mul (2 * Real.sqrt 3) (uniformSubpolynomialOn_mul hlin hsqrt)

theorem large_factor_subpolynomial (D τ : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) :
    UniformSubpolynomialOn (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ largeFactor τ B) := by
  have hbase := small_factor_subpolynomial D hD
  have htail := LogPowerExponential.uniformSubpolynomial
    (PowerSeriesTail.constant (1 + τ)) D (1 - τ)
    (PowerSeriesTail.constant_pos _ (by linarith)).le hD (by linarith) (by linarith)
  have heq : (fun _N B : ℕ ↦ largeFactor τ B) =
      (fun _N B : ℕ ↦ 4 * (smallFactor B *
        Real.exp (PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)))) := by
    funext N B
    unfold smallFactor largeFactor
    ring
  rw [heq]
  exact uniformSubpolynomialOn_const_mul 4 (uniformSubpolynomialOn_mul hbase htail)

theorem ambient_sqrt (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * Real.sqrt N = (N : ℝ) ^ (3 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow]
  calc
    (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

theorem finite_small_factor {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) (hT : 0 ≤ T) :
    ((windows N B T).card : ℝ) ≤ smallFactor B * (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
  have hfinite := SmallKernelWindows.finite_exp_bound T hN hB hT
  have heq : 2 * B * Real.sqrt (3 * N) * Real.sqrt T * Real.exp (2 * Real.sqrt B) =
      (2 * Real.sqrt 3 * B * Real.exp (2 * Real.sqrt B)) *
        (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    simp only [Real.sqrt_eq_rpow]
    ring
  rw [heq] at hfinite
  refine hfinite.trans ?_
  unfold smallFactor
  gcongr
  exact le_add_of_nonneg_right (by norm_num)

theorem finite_large_factor {N B : ℕ} (T τ : ℝ) (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hT : 0 < T) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ((bothPairs N B T).card : ℝ) ≤ largeFactor τ B * (N : ℝ) ^ (3 / 2 : ℝ) * T ^ (-1 / 2 + τ) := by
  have hfinite := LargeAnchorPairs.finite_exp_bound T τ hN hB hBN hT hτ hτhalf
  have heq : 8 * B * N * Real.sqrt (3 * N) * T ^ (-1 / 2 + τ) *
        Real.exp (2 * Real.sqrt B + PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) =
      (8 * Real.sqrt 3 * B * Real.exp (2 * Real.sqrt B) *
        Real.exp (PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ))) *
          (N : ℝ) ^ (3 / 2 : ℝ) * T ^ (-1 / 2 + τ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.exp_add, ← ambient_sqrt N (by omega)]
    ring
  rw [heq] at hfinite
  refine hfinite.trans ?_
  unfold largeFactor
  gcongr
  exact le_add_of_nonneg_right (by norm_num)

theorem uniform_counts (D τ ε : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, 1 ≤ B → B ≤ N → (B : ℝ) ≤ D * Real.log N →
      ∀ T : ℝ, 0 < T →
        ((bothPairs N B T).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) ∧
        ((windows N B T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * T ^ (1 / 2 : ℝ) := by
  obtain ⟨Ns, hNs⟩ := UniformReal.uniformSubpolynomialOn_le_rpow (small_factor_subpolynomial D hD) ε hε
  obtain ⟨Nl, hNl⟩ := UniformReal.uniformSubpolynomialOn_le_rpow (large_factor_subpolynomial D τ hD hτ hτhalf) ε hε
  refine ⟨max 2 (max Ns Nl), ?_⟩
  intro N hN B hB hBN hlog T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : smallFactor B ≤ (N : ℝ) ^ ε := (le_abs_self _).trans (hNs N (by omega) B hlog)
  have hl : largeFactor τ B ≤ (N : ℝ) ^ ε := (le_abs_self _).trans (hNl N (by omega) B hlog)
  constructor
  · refine (finite_large_factor T τ (by omega) hB hBN hT hτ hτhalf).trans ?_
    calc
      _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ (3 / 2 : ℝ)) * T ^ (-1 / 2 + τ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring
  · refine (finite_small_factor T (by omega) hBN hT.le).trans ?_
    calc
      _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ (1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem critical_counts (C τ ε : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : ℝ, 0 < T →
        ((bothPairs N (L + 1) T).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) ∧
        ((windows N (L + 1) T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * T ^ (1 / 2 : ℝ) := by
  obtain ⟨Ncount, hcount⟩ := uniform_counts upperScale τ ε upperScale_pos.le hτ hτhalf hε
  obtain ⟨Nlog, hlog⟩ := critical_band_scale C
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) 1
  refine ⟨max Ncount (max Nlog Npoly), ?_⟩
  intro N hN L hcrit T hT
  have hBN : L + 1 ≤ N := by
    have h := hpoly N (by omega) L hcrit
    simp only [pow_one, one_mul] at h
    exact_mod_cast h.le
  exact hcount N (by omega) (L + 1) (by omega) hBN (hlog N (by omega) L hcrit).2 T hT

end PaperP1.SelectedKernelCounts
