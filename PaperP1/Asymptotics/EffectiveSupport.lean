module

public import PaperP1.Asymptotics.EffectiveOrderMoments

/-! # Companion T19.5 for the actual count, without a bounded-pair-moment input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveSupport

open Filter PaperP1.Model PaperP1.EffectiveTailScale

def constant (D : ℝ) (r : ℕ) : ℝ := EffectiveOrderMoments.errorConstant + D + r + Real.log 4

theorem constant_pos {D : ℝ} (hD : 0 < D) (r : ℕ) : 0 < constant D r := by
  have hE := EffectiveOrderMoments.errorConstant_pos
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold constant
  linarith

theorem ratio_bound {N : ℕ} (hn : 0 < (N : ℝ)) (hs : 1 ≤ scale N) (D : ℝ) (r : ℕ) :
    2 * (2 * EffectiveOrderMoments.envelope N) / base (constant D r) N ≤
      Real.exp (-(D + r) * scale N) := by
  rw [base_eq_exp hn]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hs hlog
  calc
    _ = Real.exp (Real.log 4 + (Real.log N / 2 + EffectiveOrderMoments.errorConstant * scale N)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      unfold EffectiveOrderMoments.envelope
      ring
    _ ≤ Real.exp (-(D + r) * scale N) *
        Real.exp (Real.log N / 2 + constant D r * scale N) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      unfold constant
      nlinarith

theorem power_bound {N : ℕ} (hh : 1 ≤ Real.log (Real.log N)) (hs : 0 ≤ scale N)
    {T : ℝ} (hT : 0 ≤ T) :
    (Real.exp (-T * scale N)) ^ order N ≤ Real.exp (-T * Real.log N) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (order_bounds hh).1 (mul_nonneg hT hs)
  rw [mul_assoc, scale_mul_orderScale hh] at h
  nlinarith

theorem uniform_tail (C D : ℝ) (hD : 0 < D) (r : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ b : ℝ,
      base (constant D r) N ≤ b →
      CountTailBounds.probability N L b ≤ Real.exp (-(D + r) * Real.log N) ∧
        CountTailBounds.moment N L b r ≤ (N : ℝ) ^ (-D) := by
  obtain ⟨Nmom, hNmom, hmom⟩ := EffectiveOrderMoments.factorial_bound C
  obtain ⟨Nscale, _, hscale⟩ := conditions_eventually
  refine ⟨max Nmom Nscale, by omega, ?_⟩
  intro N hN L hband b hb
  obtain ⟨hH, hh, hsq, hroot⟩ := hscale N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := (scale_bounds hh hsq).1
  have hk := markov_order_bound (by linarith) hh hroot (constant_pos hD r).le
  have hbase : 0 < base (constant D r) N := by rw [base_eq_exp hn]; exact Real.exp_pos _
  have hmoment := hmom N (by omega) L hband (order N) le_rfl
  have hprob := CountTailBounds.probability_le_power N L (order N) hbase hk hmoment
  have hratio0 : 0 ≤ 2 * (2 * EffectiveOrderMoments.envelope N) / base (constant D r) N := by
    unfold EffectiveOrderMoments.envelope
    exact div_nonneg (by positivity) hbase.le
  have hprob_base := hprob.trans ((pow_le_pow_left₀ hratio0 (ratio_bound hn hs D r) _).trans
    (power_bound hh (by linarith) (by positivity : 0 ≤ D + (r : ℝ))))
  have hp := (CountTailBounds.probability_mono hb).trans hprob_base
  refine ⟨hp, ?_⟩
  calc
    _ ≤ (N : ℝ) ^ r * CountTailBounds.probability N L b := CountTailBounds.moment_le_count_power N L b r
    _ ≤ (N : ℝ) ^ r * Real.exp (-(D + r) * Real.log N) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (N : ℝ) ^ (-D) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn, ← Real.exp_add]
      congr 1
      ring

theorem rounded_tail (C D : ℝ) (hD : 0 < D) (r : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.moment N L (threshold (constant D r) N : ℝ) r ≤ (N : ℝ) ^ (-D) := by
  obtain ⟨N₀, hN₀, htail⟩ := uniform_tail C D hD r
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact (htail N hN L hband _ (Nat.le_ceil _)).2

theorem band_uniform_constant (D : ℝ) (hD : 0 < D) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.moment N L (threshold K N : ℝ) r ≤ (N : ℝ) ^ (-D) := by
  exact ⟨constant D r, constant_pos hD r, fun C ↦ rounded_tail C D hD r⟩

theorem power_comparison (K η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      base K N ≤ (N : ℝ) ^ (1 / 2 + η) := by
  have hq : Tendsto orderScale atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (Real.tendsto_log_atTop.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop)
  obtain ⟨Nq, hNq⟩ := eventually_atTop.mp (hq.eventually (eventually_ge_atTop (K / η)))
  obtain ⟨Nscale, _, hscale⟩ := conditions_eventually
  refine ⟨max 3 (max Nq Nscale), by omega, ?_⟩
  intro N hN
  obtain ⟨hH, hh, _, _⟩ := hscale N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : 0 < orderScale N := by have h := (unit_scales hh).2.1; linarith
  have hK : K / orderScale N ≤ η := by
    apply (div_le_iff₀ hq0).mpr
    have h := (div_le_iff₀ hη).mp (hNq N (by omega))
    nlinarith
  rw [base_eq_exp hn, Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ Real.log N)
  have h' : K * (Real.log N / orderScale N) ≤ η * Real.log N := by
    calc
      _ = (K / orderScale N) * Real.log N := by ring
      _ ≤ _ := h
  unfold scale
  nlinarith

theorem power_tail (C D : ℝ) (hD : 0 < D) (r : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.moment N L ((N : ℝ) ^ (1 / 2 + η)) r ≤ (N : ℝ) ^ (-D) := by
  obtain ⟨Ntail, hNtail, htail⟩ := uniform_tail C D hD r
  obtain ⟨Npower, _, hpower⟩ := power_comparison (constant D r) η hη
  refine ⟨max Ntail Npower, by omega, ?_⟩
  intro N hN L hband
  exact (htail N (by omega) L hband _ (hpower N (by omega))).2

/-- Both original conclusions, with a coefficient independent of the band width. -/
theorem companion_T19_5 (C D : ℝ) (hD : 0 < D) (r : ℕ) :
    (∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.moment N L (threshold K N : ℝ) r ≤ (N : ℝ) ^ (-D)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.moment N L ((N : ℝ) ^ (1 / 2 + η)) r ≤ (N : ℝ) ^ (-D)) := by
  exact ⟨⟨constant D r, constant_pos hD r, rounded_tail C D hD r⟩, power_tail C D hD r⟩

end PaperP1.EffectiveSupport
