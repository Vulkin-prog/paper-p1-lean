module

public import PaperP1.Asymptotics.SaturationDegreeBudget
public import PaperP1.Asymptotics.ModerateCertificateAsymptotic
public import PaperP1.Combinatorics.SaturationGraph

/-! # The actual saturation degrees uniformly over the critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaturationDegrees

open Filter PaperP1.ModerateOrder PaperP1.SaturationPrimes PaperP1.SaturationGraph

theorem finite_conditions (C A : ℝ) (hA : 1 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        10 ≤ N ∧ 2 ≤ L + 1 ∧ L + 1 ≤ N + 1 ∧
          ((L + 1 : ℕ) : ℝ) ≤ cutoff A N ∧
          ((L + 1 : ℕ) : ℝ) ≤ PaperP1.CriticalBandScale.upperScale * Real.log N := by
  obtain ⟨Ncut, hcut⟩ := eventually_atTop.mp
    (PaperP1.ModerateCertificateAsymptotic.cutoff_ge_log_eventually A PaperP1.CriticalBandScale.upperScale hA)
  obtain ⟨Nscale, hscale⟩ := PaperP1.CriticalBandScale.critical_band_scale C
  obtain ⟨Nwidth, hwidth⟩ := PaperP1.UniformFixedSourceCertificates.logarithmic_width_le_nat_eventually
    PaperP1.CriticalBandScale.upperScale PaperP1.CriticalBandScale.upperScale_pos.le
  obtain ⟨Nlog, hlog⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually
    (2 / PaperP1.CriticalBandScale.lowerScale)
  refine ⟨max 10 (max Ncut (max Nscale (max Nwidth Nlog))), ?_⟩
  intro N hN L hL
  have hband := hscale N (by omega) L hL
  have hLwidth : L ≤ N := hwidth N (by omega) L hband.2
  have htwo : (2 : ℝ) ≤ PaperP1.CriticalBandScale.lowerScale * Real.log N := by
    have h := (div_le_iff₀ PaperP1.CriticalBandScale.lowerScale_pos).mp (hlog N (by omega)).1
    nlinarith
  have hB : 2 ≤ L + 1 := by exact_mod_cast htwo.trans hband.1
  exact ⟨by omega, hB, by omega, hband.2.trans (hcut N (by omega)), hband.2⟩

/-- All three source degree bounds, with one threshold before every length and vertex. -/
theorem main_7_3 (C A ε : ℝ) (hA : 1 < A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ x ∈ Finset.Ico N (2 * N),
        ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) ∧
        ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε)) ∧
      ((graph (L + 1) N (cutoff A N)).maxDegree : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨Nbudget, hbudget⟩ := eventually_atTop.mp
    (PaperP1.SaturationDegreeBudget.product_le_power_eventually A PaperP1.CriticalBandScale.upperScale
      (2 * Real.exp 1) 2 ε (by linarith) hD (by positivity) (by norm_num) hε)
  obtain ⟨Nfinite, hfinite⟩ := finite_conditions C A hA
  refine ⟨max Nbudget Nfinite, ?_⟩
  intro N hN L hL
  obtain ⟨hN10, hB, hBN, hY, hwidth⟩ := hfinite N (by omega) L hL
  have hmaxfinite := maxDegree_bound hN10 hB hBN (cutoff A N) hY
  have hpower := hbudget N (by omega) (L + 1) (by omega) hwidth
  change 2 * (↑(L + 1) : ℝ) ^ 2 * (2 * Real.exp 1 * (↑(L + 1) : ℝ)) ^
    PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) ≤ _ at hpower
  have hmax := hmaxfinite.trans hpower
  refine ⟨?_, hmax⟩
  intro x hx
  let v : Vertex N := ⟨x, hx⟩
  obtain ⟨hout, hin⟩ := directed_degrees_le_degree (L + 1) N (cutoff A N) v
  have hdeg := (graph (L + 1) N (cutoff A N)).degree_le_maxDegree v
  have houtR : ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hout.trans hdeg
  have hinR : ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hin.trans hdeg
  exact ⟨houtR.trans hmax, hinR.trans hmax⟩

end PaperP1.SaturationDegrees
