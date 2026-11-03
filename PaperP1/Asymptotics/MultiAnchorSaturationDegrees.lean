module

public import PaperP1.Asymptotics.MultiAnchorDegreeBudget
public import PaperP1.Asymptotics.SaturationDegrees
public import PaperP1.Combinatorics.MultiAnchorGraph

/-! # Actual t-anchor saturation degrees uniformly over the critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorSaturationDegrees

open Filter PaperP1.MultiAnchorOrder PaperP1.MultiAnchorSaturation PaperP1.MultiAnchorGraph

/-- All three source degree bounds, with one threshold before every length and vertex. -/
theorem uniform_degrees (t : ℕ) (C A ε : ℝ) (ht : 1 ≤ t) (hA : 1 < A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ x ∈ Finset.Ico N (2 * N),
        ((outgoing t (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ ((t : ℝ) / A + ε) ∧
        ((incoming t (L + 1) N (cutoff A N) x).card : ℝ) ≤ (N : ℝ) ^ ((t : ℝ) / A + ε)) ∧
      ((graph t (L + 1) N (cutoff A N)).maxDegree : ℝ) ≤ (N : ℝ) ^ ((t : ℝ) / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  obtain ⟨Nbudget, hbudget⟩ := eventually_atTop.mp
    (PaperP1.MultiAnchorDegreeBudget.product_le_power_eventually t A PaperP1.CriticalBandScale.upperScale
      (2 * t * Real.exp 1) 2 ε (by linarith) hD (by positivity) (by norm_num) hε)
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  refine ⟨max Nbudget Nfinite, ?_⟩
  intro N hN L hL
  obtain ⟨hN10, hB, hBN, hY, hwidth⟩ := hfinite N (by omega) L hL
  have hmaxfinite := maxDegree_bound ht hN10 hB hBN (cutoff A N) hY
  have hpower := hbudget N (by omega) (L + 1) (by omega) hwidth
  change 2 * (↑(L + 1) : ℝ) ^ t * (2 * t * Real.exp 1 * (↑(L + 1) : ℝ)) ^
    PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N (cutoff A N) ≤ _ at hpower
  have hmax := hmaxfinite.trans hpower
  refine ⟨?_, hmax⟩
  intro x hx
  let v : Vertex N := ⟨x, hx⟩
  obtain ⟨hout, hin⟩ := directed_degrees_le_degree t (L + 1) N (cutoff A N) v
  have hdeg := (graph t (L + 1) N (cutoff A N)).degree_le_maxDegree v
  have houtR : ((outgoing t (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph t (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hout.trans hdeg
  have hinR : ((incoming t (L + 1) N (cutoff A N) x).card : ℝ) ≤
      (graph t (L + 1) N (cutoff A N)).maxDegree := by exact_mod_cast hin.trans hdeg
  exact ⟨houtR.trans hmax, hinR.trans hmax⟩

end PaperP1.MultiAnchorSaturationDegrees
