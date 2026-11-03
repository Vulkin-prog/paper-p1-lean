module

public import PaperP1.Model.MultiAnchorFamilyMass
public import PaperP1.Asymptotics.MultiAnchorCertificateAsymptotic
public import PaperP1.Asymptotics.SaturationDegrees

/-! # Actual unordered moderate mass with t anchors and heterogeneous weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorModerateMass

open Finset Filter PaperP1.Model PaperP1.MultiAnchorFamilyMass

theorem uniform_bound (t : ℕ) (C M A β ε : ℝ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hA : 1 < A) (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧
        Certified t I.card (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε) := by
  have hD : 1 ≤ PaperP1.CriticalBandScale.upperScale := by
    unfold PaperP1.CriticalBandScale.upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  obtain ⟨NM, hm⟩ := eventually_atTop.mp
    (PaperP1.MultiAnchorCertificateAsymptotic.weightedTotal_le_power_eventually
      t A β PaperP1.CriticalBandScale.upperScale M ε ht hA hβ hD hε)
  refine ⟨10 + NF + NM, by omega, ?_⟩
  intro N hN L hband p hp hcap F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨_hN10, hB, hBN, _hY, hwidth⟩ := hf N (by omega) L hband
  have hmass := certified_total_bound t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β)
    F (fun I hI ↦ (hF I hI).1) (fun I hI ↦ (hF I hI).2)
    p hp (M / N) (div_nonneg hM hn.le) hcap
  exact hmass.trans (hm N (by omega) (L + 1) hB hBN hwidth (M / N)
    (div_nonneg hM hn.le) (by rw [div_mul_cancel₀ _ hn.ne']))

end PaperP1.MultiAnchorModerateMass
