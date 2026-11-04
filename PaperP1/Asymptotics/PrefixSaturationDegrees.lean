module

public import PaperP1.Asymptotics.SaturationDegreeBudget
public import PaperP1.Asymptotics.ModerateCertificateAsymptotic
public import PaperP1.Combinatorics.PrefixSaturationGraph

/-! # Saturation degrees on the positive prefix at every logarithmic width

There is no critical-band lower restriction on the window length or centre.
The threshold precedes every permitted width and every actual prefix vertex.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixSaturationDegrees

open Filter PaperP1.ModerateOrder PaperP1.PrefixSaturationPrimes PaperP1.PrefixSaturationGraph

theorem finite_conditions (D A : ℝ) (hD : 1 ≤ D) (hA : 1 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 1 ≤ L →
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      10 ≤ N ∧ 2 ≤ L + 1 ∧ L + 1 ≤ N + 1 ∧ ((L + 1 : ℕ) : ℝ) ≤ cutoff A N := by
  obtain ⟨NC, hc⟩ := eventually_atTop.mp (ModerateCertificateAsymptotic.cutoff_ge_log_eventually A D hA)
  obtain ⟨NW, hw⟩ := UniformFixedSourceCertificates.logarithmic_width_le_nat_eventually D (zero_le_one.trans hD)
  refine ⟨max 10 (max NC NW), ?_⟩
  intro N hN L hL hwidth
  have hLN := hw N (by omega) L hwidth
  exact ⟨by omega, by omega, by omega, hwidth.trans (hc N (by omega))⟩

theorem uniform_degrees (D A ε : ℝ) (hD : 1 ≤ D) (hA : 1 < A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 1 ≤ L →
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      (∀ x ∈ Finset.Ico 2 (N + 2),
        ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) ∧
        ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ (2 / A + ε)) ∧
      ((graph (L + 1) N (cutoff A N)).maxDegree : ℝ) ≤ (N : ℝ) ^ (2 / A + ε) := by
  obtain ⟨NB, hb⟩ := eventually_atTop.mp (SaturationDegreeBudget.product_le_power_eventually
    A D (2 * Real.exp 1) 2 ε (by linarith) hD (by positivity) (by norm_num) hε)
  obtain ⟨NF, hf⟩ := finite_conditions D A hD hA
  refine ⟨max NB NF, ?_⟩
  intro N hN L hL hwidth
  obtain ⟨hN10, hB, hBN, hY⟩ := hf N (by omega) L hL hwidth
  have hmax := maxDegree_bound hN10 hB hBN (cutoff A N) hY
  have hpower := hb N (by omega) (L + 1) (by omega) hwidth
  change 2 * (↑(L + 1) : ℝ) ^ 2 * (2 * Real.exp 1 * (↑(L + 1) : ℝ)) ^
    PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) ≤ _ at hpower
  have hbound := hmax.trans hpower
  refine ⟨?_, hbound⟩
  intro x hx
  let v : Vertex N := ⟨x, hx⟩
  obtain ⟨hout, hin⟩ := directed_degrees_le_degree (L + 1) N (cutoff A N) v
  have hdeg := (graph (L + 1) N (cutoff A N)).degree_le_maxDegree v
  have houtR : ((outgoing (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hout.trans hdeg
  have hinR : ((incoming (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hin.trans hdeg
  exact ⟨houtR.trans hbound, hinR.trans hbound⟩

end PaperP1.PrefixSaturationDegrees
