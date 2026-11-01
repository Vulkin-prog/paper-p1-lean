module

public import PaperP1.Arithmetic.SeveralAnchorConfigurations
public import PaperP1.Asymptotics.SelectedKernelCounts

/-! # The proved large-selected-kernel branch of fixed-support tuple counting -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralAnchorCounts

open PaperP1 PaperP1.ExpSqrtLog PaperP1.CriticalBandScale

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def factor (m : ℕ) (τ : ℝ) (B : ℕ) : ℝ :=
  4 ^ m * Real.sqrt 3 * (B + 1) * Real.exp (2 * Real.sqrt B) *
    Real.exp (m * PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ))

theorem factor_subpolynomial (m : ℕ) (D τ : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    UniformSubpolynomialOn (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ factor m τ B) := by
  have hlin := uniformSubpolynomialOn_linear_log_add_one
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) D hD (fun _ _ h ↦ h)
  have hsqrt := uniformSubpolynomialOn_exp_sqrt_of_le_log
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) 2 D (by norm_num) hD (fun _ _ h ↦ h)
  have htail := LogPowerExponential.uniformSubpolynomial
    (m * PowerSeriesTail.constant (1 + τ)) D (1 - τ)
    (mul_nonneg (Nat.cast_nonneg m) (PowerSeriesTail.constant_pos _ (by linarith)).le)
    hD (by linarith) (by linarith)
  simpa only [factor, mul_assoc] using uniformSubpolynomialOn_const_mul
    (4 ^ m * Real.sqrt 3) (uniformSubpolynomialOn_mul (uniformSubpolynomialOn_mul hlin hsqrt) htail)

theorem ambient_sqrt (N m : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ m * Real.sqrt N = (N : ℝ) ^ ((m : ℝ) + 1 / 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn]

theorem finite_factor_bound {N B : ℕ} (T τ : ℝ) (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hT : 0 < T) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ((PaperP1.SeveralAnchorConfigurations.configurations (ι := ι) N B T).card : ℝ) ≤
      factor (Fintype.card ι) τ B * (N : ℝ) ^ ((Fintype.card ι : ℝ) + 1 / 2) * T ^ (-1 / 2 + τ) := by
  have hfinite := PaperP1.SeveralAnchorConfigurations.finite_exp_bound (ι := ι) T τ hN hB hBN hT hτ hτhalf
  have heq : 4 ^ Fintype.card ι * B * (N : ℝ) ^ Fintype.card ι * Real.sqrt (3 * N) * T ^ (-1 / 2 + τ) *
      Real.exp (2 * Real.sqrt B + Fintype.card ι * PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) =
      (4 ^ Fintype.card ι * Real.sqrt 3 * B * Real.exp (2 * Real.sqrt B) *
        Real.exp (Fintype.card ι * PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ))) *
          (N : ℝ) ^ ((Fintype.card ι : ℝ) + 1 / 2) * T ^ (-1 / 2 + τ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.exp_add, ← ambient_sqrt N (Fintype.card ι) (by omega)]
    ring
  rw [heq] at hfinite
  refine hfinite.trans ?_
  unfold factor
  gcongr
  exact le_add_of_nonneg_right (by norm_num)

theorem uniform_count (D τ ε : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, 1 ≤ B → B ≤ N → (B : ℝ) ≤ D * Real.log N →
      ∀ T : ℝ, 0 < T →
        ((PaperP1.SeveralAnchorConfigurations.configurations (ι := ι) N B T).card : ℝ) ≤
          (N : ℝ) ^ ((Fintype.card ι : ℝ) + 1 / 2 + ε) * T ^ (-1 / 2 + τ) := by
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow
    (factor_subpolynomial (Fintype.card ι) D τ hD hτ hτhalf) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN B hB hBN hlog T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : factor (Fintype.card ι) τ B ≤ (N : ℝ) ^ ε :=
    (le_abs_self _).trans (hN₀ N (by omega) B hlog)
  refine (finite_factor_bound (ι := ι) T τ (by omega) hB hBN hT hτ hτhalf).trans ?_
  calc
    _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ ((Fintype.card ι : ℝ) + 1 / 2)) * T ^ (-1 / 2 + τ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem critical_count (C τ ε : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : ℝ, 0 < T →
        ((PaperP1.SeveralAnchorConfigurations.configurations (ι := ι) N (L + 1) T).card : ℝ) ≤
          (N : ℝ) ^ ((Fintype.card ι : ℝ) + 1 / 2 + ε) * T ^ (-1 / 2 + τ) := by
  obtain ⟨Ncount, hcount⟩ := uniform_count (ι := ι) upperScale τ ε upperScale_pos.le hτ hτhalf hε
  obtain ⟨Nlog, hlog⟩ := critical_band_scale C
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) 1
  refine ⟨max Ncount (max Nlog Npoly), ?_⟩
  intro N hN L hcrit T hT
  have hBN : L + 1 ≤ N := by
    have h := hpoly N (by omega) L hcrit
    simp only [pow_one, one_mul] at h
    exact_mod_cast h.le
  exact hcount N (by omega) (L + 1) (by omega) hBN (hlog N (by omega) L hcrit).2 T hT

end PaperP1.SeveralAnchorCounts
