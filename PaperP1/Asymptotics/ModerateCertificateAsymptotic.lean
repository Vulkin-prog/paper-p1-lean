module

public import PaperP1.Asymptotics.ModerateFactorialBudget
public import PaperP1.Arithmetic.ModerateWeightedSeries
public import PaperP1.Model.LocalRigidityConsequences

/-! # The weighted growing-order conclusion of the moderate-certificate lemma -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateCertificateAsymptotic

open Filter PaperP1.ModerateOrder PaperP1.ModerateWeightedSeries

theorem constant_le_power_eventually (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ ε :=
  ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop K)

theorem cutoff_ge_log_eventually (A D : ℝ) (hA : 1 < A) :
    ∀ᶠ N : ℕ in atTop, D * Real.log N ≤ cutoff A N := by
  have hlim := (tendsto_rpow_atTop (by linarith : 0 < A - 1)).comp
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop D),
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N h hH
  have hHpos : 0 < Real.log N := by linarith
  calc
    _ ≤ (Real.log N) ^ (A - 1) * Real.log N := mul_le_mul_of_nonneg_right h hHpos.le
    _ = (Real.log N) ^ ((A - 1) + 1) := by rw [Real.rpow_add hHpos, Real.rpow_one]
    _ = cutoff A N := by unfold cutoff; congr 1; ring

def exponentialConstant (M : ℝ) : ℝ := 18 * Real.exp (Real.exp 1 * (2 * M))

theorem weightedTotal_le_power_eventually (A β D M ε : ℝ)
    (hA : 1 < A) (hβ : 0 ≤ β) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 2 ≤ B → B ≤ N + 1 → (B : ℝ) ≤ D * Real.log N →
      ∀ a : ℝ, 0 ≤ a → a * N ≤ M →
        weightedTotal B N (cutoff A N) ((N : ℝ) ^ β) a ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [PaperP1.ModerateFactorialBudget.product_le_power_eventually A D (ε / 2)
      (by linarith) hD hhalf,
    cutoff_ge_log_eventually A D hA,
    constant_le_power_eventually (exponentialConstant M) (ε / 2) hhalf,
    eventually_ge_atTop 10] with N hbudget hcut hconstant hN B hB hBN hwidth a ha hmean
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT : 1 ≤ (N : ℝ) ^ β := Real.one_le_rpow hNone hβ
  have hY := hwidth.trans hcut
  have hfinite := weightedTotal_le B N hN hB hBN (cutoff A N) ((N : ℝ) ^ β) a hY hT ha
  have hexp : Real.exp (Real.exp 1 * (2 * a * N)) ≤ Real.exp (Real.exp 1 * (2 * M)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmean (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)
    nlinarith
  have hpref : 0 ≤ coefficient B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) + 1).factorial : ℝ) := by
    unfold coefficient
    positivity
  have hfinite' := hfinite.trans (mul_le_mul_of_nonneg_left hexp hpref)
  have hdenom : ((N : ℝ) ^ β) ^ 2 = (N : ℝ) ^ (2 * β) := by
    rw [← Real.rpow_mul_natCast hNpos.le β 2]
    congr 1
    ring
  have hrew : coefficient B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) + 1).factorial : ℝ) *
        Real.exp (Real.exp 1 * (2 * M)) =
      exponentialConstant M * ((B : ℝ) ^ (order A N + 4) * ((order A N + 1).factorial : ℝ)) /
        (N : ℝ) ^ (2 * β) := by
    unfold coefficient exponentialConstant order
    rw [hdenom]
    ring
  rw [hrew] at hfinite'
  have hprod := hbudget B (by omega) hwidth
  have hK : 0 ≤ exponentialConstant M := by unfold exponentialConstant; positivity
  calc
    _ ≤ exponentialConstant M *
        ((B : ℝ) ^ (order A N + 4) * ((order A N + 1).factorial : ℝ)) / (N : ℝ) ^ (2 * β) := hfinite'
    _ ≤ exponentialConstant M * (N : ℝ) ^ (4 / A + ε / 2) / (N : ℝ) ^ (2 * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hK) (Real.rpow_nonneg hNpos.le _)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (4 / A + ε / 2) / (N : ℝ) ^ (2 * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNpos.le _))
        (Real.rpow_nonneg hNpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring

theorem weighted_criticalBand (C A β u ε : ℝ)
    (hA : 1 < A) (hβ : 0 ≤ β) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        weightedTotal (L + 1) N (cutoff A N) ((N : ℝ) ^ β) (u * (2 ^ L : ℝ)⁻¹) ≤
          (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨Nweight, hweight⟩ := eventually_atTop.mp
    (weightedTotal_le_power_eventually A β PaperP1.CriticalBandScale.upperScale
      (u * (2 : ℝ) ^ C) ε hA hβ hD hε)
  obtain ⟨Nscale, hscale⟩ := PaperP1.CriticalBandScale.critical_band_scale C
  obtain ⟨Nwidth, hwidth⟩ := PaperP1.UniformFixedSourceCertificates.logarithmic_width_le_nat_eventually
    PaperP1.CriticalBandScale.upperScale PaperP1.CriticalBandScale.upperScale_pos.le
  obtain ⟨Nlog, hlog⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually
    (2 / PaperP1.CriticalBandScale.lowerScale)
  refine ⟨max 10 (max Nweight (max Nscale (max Nwidth Nlog))), ?_⟩
  intro N hN L hL
  have hband := hscale N (by omega) L hL
  have hLwidth : L ≤ N := hwidth N (by omega) L hband.2
  have htwo : (2 : ℝ) ≤ PaperP1.CriticalBandScale.lowerScale * Real.log N := by
    have h := (div_le_iff₀ PaperP1.CriticalBandScale.lowerScale_pos).mp (hlog N (by omega)).1
    nlinarith
  have hB : 2 ≤ L + 1 := by exact_mod_cast htwo.trans hband.1
  apply hweight N (by omega) (L + 1) hB (by omega) hband.2
  · positivity
  · have hnom := PaperP1.LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hL
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc
      _ ≤ (u * ((2 : ℝ) ^ C / N)) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnom hu) hNpos.le
      _ = _ := by field_simp

/-- Both conclusions of article Lemma 7.2, with an explicit epsilon meaning of o(1).
The threshold precedes every critical-band length and every finite counting order. -/
theorem main_7_2 (C A β u ε : ℝ)
    (hA : 1 < A) (hβ : 0 < β) (_hβone : β < 1) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ r : ℕ, 1 ≤ r → ∀ Y T : ℝ, ((L + 1 : ℕ) : ℝ) ≤ Y → 1 ≤ T →
        ((PaperP1.ModerateCertificateCount.sourceTuples r (L + 1) N Y T).card : ℝ) ≤
          36 * (r : ℝ) * (L + 1 : ℝ) ^ 4 * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ 2 *
            (↑(r * (L + 1)) : ℝ) ^ PaperP1.PrimeProductBudget.assignmentExponent N Y) ∧
      (∑' r : ℕ, weightedTerm (L + 1) N (cutoff A N) ((N : ℝ) ^ β)
        (u * (2 ^ L : ℝ)⁻¹) (r + 1)) ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.ModerateCertificateCount.main_7_2_finite_criticalBand C
  obtain ⟨Nweight, hweight⟩ := weighted_criticalBand C A β u ε hA hβ.le hu.le hε
  refine ⟨max Nfinite Nweight, ?_⟩
  intro N hN L hL
  refine ⟨hfinite N (by omega) L hL, ?_⟩
  rw [← weightedTotal_eq_positiveOrders]
  exact hweight N (by omega) L hL

end PaperP1.ModerateCertificateAsymptotic
