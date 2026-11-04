module

public import PaperP1.Arithmetic.TruncatedAsymmetricSupport
public import PaperP1.Asymptotics.TruncatedAnchorPairCount
public import PaperP1.Asymptotics.ComparableTranslatedKernelCounts

/-! # Unconditional four-thirds support on a fixed comparable interval

This counts the support of relations. It is not the weighted profile.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableTruncatedSupportCount

open PaperP1.TruncatedAsymmetricSupport PaperP1.TranslatedKernelWindows

theorem uniform_count (Q : ℕ) (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H U : ℕ,
      1 ≤ H → H ≤ N → 2 ≤ U → U ≤ N → N ≤ Q * (U - 1) →
      (H : ℝ) ≤ D * Real.log N → (population N H U).card ≤ (N : ℝ) ^ (4 / 3 + ε) := by
  let η := min (ε / 8) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨Na, ha⟩ := TruncatedAnchorPairCount.uniform_count D η η hD hη hηhalf hη
  obtain ⟨No, ho⟩ := TranslatedKernelCounts.one_uniform D η hD hη
  obtain ⟨Nt, _hNt, ht⟩ := ComparableTranslatedKernelCounts.two_uniform_budget Q D η hη
  obtain ⟨Nd, hd⟩ := TwoDefectCount.two_defect_count_le_rpow_eventually 2 D D (by norm_num) hD hD η hη
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 4 (4 / 3 + 2 * η) (ε - 2 * η) (by linarith)
  refine ⟨max 4 (max Na (max No (max Nt (max Nd Nf)))), by omega, ?_⟩
  intro N hN H U hH hHN hU hUN hUratio hlog
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let T : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  have hT : 0 < T := Real.rpow_pos_of_pos hn _
  have hlarge : ((TruncatedAnchorPairs.bothPairs N H U T).card : ℝ) ≤ (N : ℝ) ^ (4 / 3 + 2 * η) := by
    refine (ha N (by omega) H U hH hHN hU hUN hlog T hT).trans ?_
    dsimp [T]
    rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    linarith
  have hone : ((oneStarts N H U T).card : ℝ) ≤ (N : ℝ) ^ (2 / 3 + η) := by
    refine (ho N (by omega) H U hHN hU hUN hlog T hT.le).trans_eq ?_
    dsimp [T]
    rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    ring
  have htwo : ((twoStarts N H U T).card : ℝ) ≤ 2 * (N : ℝ) ^ (2 / 3 + η) := by
    refine (ht N (by omega) H U hHN hU hUN hUratio hlog T hT.le).trans ?_
    have hTsmall : T ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)
    calc
      _ ≤ (2 * (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ η := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hTsmall]) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hn]
  have hproduct : ((oneStarts N H U T).card : ℝ) * (twoStarts N H U T).card ≤
      2 * (N : ℝ) ^ (4 / 3 + 2 * η) := by
    calc
      _ ≤ (N : ℝ) ^ (2 / 3 + η) * (2 * (N : ℝ) ^ (2 / 3 + η)) :=
        mul_le_mul hone htwo (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hn,
          show (2 / 3 + η) + (2 / 3 + η) = (4 / 3 : ℝ) + 2 * η by ring]
  have hdefect : ((defectStarts N H U).card : ℝ) ≤ (N : ℝ) ^ η := by
    calc
      _ ≤ ((TwoDefectHosts.twoDefectStarts H H (2 * N)).card : ℝ) := by
        exact_mod_cast defect_card N H U hU
      _ ≤ _ := hd N (by omega) H H (2 * N) hlog hlog (by push_cast; linarith)
  have hdefect_product : (N : ℝ) * (defectStarts N H U).card ≤ (N : ℝ) ^ (4 / 3 + 2 * η) := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ η := mul_le_mul_of_nonneg_left hdefect hn.le
      _ = (N : ℝ) ^ (1 + η) := by rw [Real.rpow_add hn, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hfinite : ((population N H U).card : ℝ) ≤ (TruncatedAnchorPairs.bothPairs N H U T).card +
      ((oneStarts N H U T).card : ℝ) * (twoStarts N H U T).card + (N : ℝ) * (defectStarts N H U).card := by
    exact_mod_cast population_card N H U T hU hUN
  have htotal : ((population N H U).card : ℝ) ≤ 4 * (N : ℝ) ^ (4 / 3 + 2 * η) := by
    linarith only [hfinite, hlarge, hproduct, hdefect_product]
  exact htotal.trans (by
    simpa only [show (4 / 3 + 2 * η) + (ε - 2 * η) = 4 / 3 + ε by ring] using hf N (by omega))

end PaperP1.ComparableTruncatedSupportCount
