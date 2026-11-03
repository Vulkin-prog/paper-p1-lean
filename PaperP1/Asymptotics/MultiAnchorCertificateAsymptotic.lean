module

public import PaperP1.Asymptotics.MultiAnchorFactorialBudget
public import PaperP1.Arithmetic.MultiAnchorWeightedSeries
public import PaperP1.Model.LocalRigidityConsequences

/-! # The all-order moderate certificate budget with t anchors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorCertificateAsymptotic

open Filter PaperP1.MultiAnchorOrder PaperP1.MultiAnchorWeightedSeries

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
    _ = cutoff A N := by unfold cutoff PaperP1.ModerateOrder.cutoff; congr 1; ring

def exponentialConstant (t : ℕ) (M : ℝ) : ℝ := (6 : ℝ) ^ t / 2 * Real.exp (Real.exp 1 * (2 * M))

theorem weightedTotal_le_power_eventually (t : ℕ) (A β D M ε : ℝ)
    (ht : 1 ≤ t) (hA : 1 < A) (hβ : 0 ≤ β) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 2 ≤ B → B ≤ N + 1 → (B : ℝ) ≤ D * Real.log N →
      ∀ a : ℝ, 0 ≤ a → a * N ≤ M →
        weightedTotal t B N (cutoff A N) ((N : ℝ) ^ β) a ≤ (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε) := by
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [PaperP1.MultiAnchorFactorialBudget.product_le_power_eventually t A D (ε / 2)
      (by linarith) hD hhalf,
    cutoff_ge_log_eventually A D hA,
    constant_le_power_eventually (exponentialConstant t M) (ε / 2) hhalf,
    eventually_ge_atTop (3 ^ t + 1)] with N hbudget hcut hconstant hN B hB hBN hwidth a ha hmean
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT : 1 ≤ (N : ℝ) ^ β := Real.one_le_rpow hNone hβ
  have hY := hwidth.trans hcut
  have hfinite := weightedTotal_le t B N ht (by omega) hB hBN (cutoff A N) ((N : ℝ) ^ β) a hY hT ha
  have hexp : Real.exp (Real.exp 1 * (2 * a * N)) ≤ Real.exp (Real.exp 1 * (2 * M)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmean (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)
    nlinarith
  have hpref : 0 ≤ coefficient t B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N (cutoff A N) + 1).factorial : ℝ) := by
    unfold coefficient
    positivity
  have hfinite' := hfinite.trans (mul_le_mul_of_nonneg_left hexp hpref)
  have hdenom : ((N : ℝ) ^ β) ^ t = (N : ℝ) ^ ((t : ℝ) * β) := by
    rw [← Real.rpow_mul_natCast hNpos.le β t]
    congr 1
    ring
  have hrew : coefficient t B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N (cutoff A N) + 1).factorial : ℝ) *
        Real.exp (Real.exp 1 * (2 * M)) =
      exponentialConstant t M * ((B : ℝ) ^ (order t A N + 2 * t) * ((order t A N + 1).factorial : ℝ)) /
        (N : ℝ) ^ ((t : ℝ) * β) := by
    unfold coefficient exponentialConstant order
    rw [hdenom]
    ring
  rw [hrew] at hfinite'
  have hprod := hbudget B (by omega) hwidth
  have hK : 0 ≤ exponentialConstant t M := by unfold exponentialConstant; positivity
  calc
    _ ≤ exponentialConstant t M *
        ((B : ℝ) ^ (order t A N + 2 * t) * ((order t A N + 1).factorial : ℝ)) / (N : ℝ) ^ ((t : ℝ) * β) := hfinite'
    _ ≤ exponentialConstant t M * (N : ℝ) ^ (2 * (t : ℝ) / A + ε / 2) / (N : ℝ) ^ ((t : ℝ) * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hK) (Real.rpow_nonneg hNpos.le _)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (2 * (t : ℝ) / A + ε / 2) / (N : ℝ) ^ ((t : ℝ) * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNpos.le _))
        (Real.rpow_nonneg hNpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring

theorem weighted_criticalBand (t : ℕ) (C A β u ε : ℝ)
    (ht : 1 ≤ t) (hA : 1 < A) (hβ : 0 ≤ β) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        weightedTotal t (L + 1) N (cutoff A N) ((N : ℝ) ^ β) (u * (2 ^ L : ℝ)⁻¹) ≤
          (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨Nweight, hweight⟩ := eventually_atTop.mp
    (weightedTotal_le_power_eventually t A β PaperP1.CriticalBandScale.upperScale
      (u * (2 : ℝ) ^ C) ε ht hA hβ hD hε)
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

end PaperP1.MultiAnchorCertificateAsymptotic
