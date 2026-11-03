module

public import PaperP1.Asymptotics.SharpCovarianceScaleUnderInputs
public import PaperP1.Asymptotics.PoissonCharlierConversion

/-! # The literal retained-reference Poisson--Charlier conversion at the actual nominal correction scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpRetainedConversionUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.RetainedReferenceTheorem PaperP1.SecondFactorialCorrection PaperP1.FinitePairDeficitInputs

theorem companion_T17_4 (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        (∑' k : ℕ, |(FiniteLawEmbedding.embed (binomialReference H N L) -
          QuadraticPoisson.reference (countMoment (RegularStarts.regularStarts N L) L 1)
            (RegularCumulantTransfer.secondFactorialCumulant (RegularStarts.regularStarts N L) L)) {k}|) ≤
          4 * |beta H N L - regularCovariance N L| + K * (1 / (N : ℝ) ^ 2 + value N L / N) := by
  obtain ⟨p, hp⟩ := SharpCovarianceScaleUnderInputs.uniform_regular_covariance C
  obtain ⟨NF, hf⟩ := PoissonCharlierConversion.actual_regular_bound C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let E := PoissonCharlierConversion.errorConstant C
  have hE : 0 < E := PoissonCharlierConversion.errorConstant_pos C
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨R, hR, NR, _hNR, hr⟩ := hp hgeo
  refine ⟨E * (1 + R), by positivity, 3 + NF + NG + NR, by omega, ?_⟩
  intro N hN L hband H
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  obtain ⟨hpos, hcov⟩ := hr N (by omega) L hband
  have hconv := hf N (by omega) L hband H (regularCovariance N L)
  dsimp only at hconv
  rw [← regular_mean hNtwo hL, ← regular_cumulant hNtwo hL] at hconv
  have hquot : |regularCovariance N L| / N ≤ R * value N L / N :=
    div_le_div_of_nonneg_right hcov hn.le
  have hcross : 0 ≤ R * (1 / (N : ℝ) ^ 2) + value N L / N :=
    add_nonneg (mul_nonneg hR.le (by positivity)) (div_nonneg hpos.le hn.le)
  have herror : 1 / (N : ℝ) ^ 2 + R * value N L / N ≤
      (1 + R) * (1 / (N : ℝ) ^ 2 + value N L / N) := by
    simp only [div_eq_mul_inv] at hcross ⊢
    nlinarith only [hcross]
  calc
    _ ≤ 4 * |beta H N L - regularCovariance N L| +
        E * (1 / (N : ℝ) ^ 2 + |regularCovariance N L| / N) := hconv
    _ ≤ 4 * |beta H N L - regularCovariance N L| +
        E * (1 / (N : ℝ) ^ 2 + R * value N L / N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hquot) hE.le)
    _ ≤ 4 * |beta H N L - regularCovariance N L| +
        E * ((1 + R) * (1 / (N : ℝ) ^ 2 + value N L / N)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left herror hE.le)
    _ = _ := by ring

end PaperP1.SharpRetainedConversionUnderInputs
