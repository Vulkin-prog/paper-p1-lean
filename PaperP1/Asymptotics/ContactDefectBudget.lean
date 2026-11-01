module

public import PaperP1.Arithmetic.ContactWindowSpan
public import PaperP1.Coding.LocalDefectAsymptotic
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.LogarithmicDefectPower

/-! # The full union of two exact-contact windows has only a subpower relation cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactDefectBudget

open Finset PaperP1.Arithmetic PaperP1.CriticalBandScale

theorem defect_count :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ Ico N (2 * N),
        ((LocalRigidityCode.defectValues (x - 1) (2 * L + 1)).card : ℝ) ≤
          K * Real.log N / Real.log (Real.log N) := by
  have hupper := upperScale_pos
  obtain ⟨K, hK, ND, hND⟩ := LocalDefectAsymptotic.local_defect_count_le_log_div_loglog_eventually
    (1 / 2) 2 (2 * upperScale) (2 * upperScale) (by norm_num) (by norm_num) (by positivity) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro C
  obtain ⟨NG, hNG⟩ := critical_band_scale C
  refine ⟨max ND (max NG 2), ?_⟩
  intro N hN L hband x hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  have hB := (hNG N (by omega) L hband).2
  have hH : ((2 * L + 1 : ℕ) : ℝ) ≤ (2 * upperScale) * Real.log N := by
    push_cast at hB ⊢
    nlinarith only [hB]
  have hR : ((2 * L : ℕ) : ℝ) ≤ (2 * upperScale) * Real.log N := by
    push_cast at hB ⊢
    nlinarith only [hB]
  have hNat : N ≤ 2 * (x - 1) := by omega
  have hUlo : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    have h : (N : ℝ) ≤ 2 * ((x - 1 : ℕ) : ℝ) := by exact_mod_cast hNat
    linarith only [h]
  have hUhi : ((x - 1 : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast (show x - 1 ≤ 2 * N by omega)
  simpa only [LocalRigidityCode.defectValues, Nat.add_sub_cancel] using
    hND N (by omega) (2 * L + 1) (x - 1) (2 * L) hH hR hUlo hUhi

theorem relation_power (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ Ico N (2 * N),
        (2 ^ Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (2 * L + 1)) : ℝ) ≤
          (N : ℝ) ^ ε := by
  obtain ⟨K, hK, hdef⟩ := defect_count
  obtain ⟨ND, hND⟩ := hdef C
  obtain ⟨NP, hNP⟩ := LogarithmicDefectPower.uniform_power K ε hK.le hε
  refine ⟨max ND NP, ?_⟩
  intro N hN L hband x hx
  apply hNP N (by omega)
  exact (show (Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (2 * L + 1)) : ℝ) ≤
    (LocalRigidityCode.defectValues (x - 1) (2 * L + 1)).card by
      exact_mod_cast ContactWindowSpan.relation_rank_le_defects (x := x - 1) (B := 2 * L + 1) (by omega)).trans
    (hND N (by omega) L hband x hx)

end PaperP1.ContactDefectBudget
